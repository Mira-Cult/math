#!/usr/bin/env python3
"""Exact finite checks for manuscripts/cofactor-dispersion.md.

The script checks identities using integer/Fraction arithmetic and independently
enumerated products. It does not check an asymptotic bound, signed cancellation,
or primality. In particular its small examples need not satisfy the manuscript's
asymptotic relation Y <= X**(1/64).
"""

from collections import defaultdict
from fractions import Fraction
from itertools import product
from math import gcd


def require(condition, message):
    if not condition:
        raise ValueError(message)


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def liouville(n):
    """A completely multiplicative real unit phase, computed exactly."""
    sign = 1
    p = 2
    while p * p <= n:
        while n % p == 0:
            n //= p
            sign = -sign
        p += 1
    return -sign if n > 1 else sign


def product_coefficients(case):
    coefficient = defaultdict(int)
    terms = []
    for u, v in product(case["alpha"], case["beta"]):
        n = u * v
        if case["X"] < n <= 2 * case["X"] and n % case["Q"] == case["a"]:
            value = case["alpha"][u] * case["beta"][v]
            coefficient[n] += value
            terms.append((u, v, value))
    return coefficient, terms


def check_case(case):
    X, gap, weights = case["X"], case["gap"], case["weights"]
    require(all(gcd(A, gap) == 1 for A in weights), "Auxiliary/gap coprimality")
    coefficient, terms = product_coefficients(case)
    bound = (2 * X + gap) // min(weights)
    cofactor_sets = (
        set(range(1, bound + 1)),
        {c for c in range(1, bound + 1) if gcd(c, case["Q"] * gap) == 1},
        {c for c in range(1, bound + 1) if c % 3 == 1},
    )
    cutoffs = [Fraction(0), Fraction(1, 3), Fraction(1), Fraction(15, 2),
               Fraction(X, 2), Fraction(X), Fraction(2 * X), Fraction(3 * X)]
    checks = overlap_count = 0
    base = {}
    for k in range(1, bound + 1):
        base[k] = sum(w * coefficient.get(A * k - gap, 0) for A, w in weights.items())

    for cutoff, cofactors in product(cutoffs, cofactor_sets):
        # Direct expansion in the original u,v,A,c variables. The common h
        # is obtained only when c*A divides u*v+gap.
        direct = defaultdict(int)
        for (u, v, value), (A, weight), c in product(terms, weights.items(), cofactors):
            numerator = u * v + gap
            if numerator % (c * A) == 0:
                h = numerator // (c * A)
                if A * h > cutoff:
                    direct[c, h] += weight * value
                    if value and gcd(A, c) > 1:
                        overlap_count += 1
        direct_energy = sum(value * value for value in direct.values())

        # Regroup first by the integer common quotient k; c then runs over
        # divisors of k, and the moving cutoff is A*k/c > cutoff.
        regrouped_energy = 0
        expanded_diagonal = expanded_off_diagonal = 0
        for k in range(1, bound + 1):
            for c in divisors(k):
                if c not in cofactors:
                    continue
                h = k // c
                row = {
                    A: weight * coefficient.get(A * k - gap, 0)
                    for A, weight in weights.items()
                    if A * h > cutoff
                }
                row_sum = sum(row.values())
                require(row_sum == direct[c, h], "Exact moving-cutoff row")
                checks += 1
                regrouped_energy += row_sum * row_sum
                for A, B in product(row, repeat=2):
                    term = row[A] * row[B]
                    if A == B:
                        expanded_diagonal += term
                    else:
                        expanded_off_diagonal += term
        require(direct_energy == regrouped_energy, "Cofactor square regrouping")
        require(direct_energy == expanded_diagonal + expanded_off_diagonal,
                "Diagonal plus off-diagonal expansion")
        checks += 2

        if cutoff == 0:
            divisor_weighted = sum(
                sum(c in cofactors for c in divisors(k)) * value * value
                for k, value in base.items()
            )
            require(direct_energy == divisor_weighted, "Uncut divisor-weight identity")
            checks += 1

        U = cutoff.numerator // cutoff.denominator + Fraction(1, 2)
        for d in range(1, 3 * X + 1):
            require((d > cutoff) == (d > U), "Half-integer cutoff centering")
            require(d != U, "Half-integer separation")
            checks += 2
    return checks, overlap_count


def check_adapter_exception():
    # The older determinant-plus-one-congruence replacement needs (A,c)=1.
    # The exact quotient formulation retains these variables without that
    # assumption. Here its common quotient is 4, which is not a multiple of 3.
    gap, A, B, c, uv, rs = 2, 3, 5, 3, 10, 18
    require(B * uv - A * rs == gap * (A - B), "Counterexample determinant")
    require((uv + gap) % c == 0, "Counterexample single congruence")
    require(gcd(A, B) == 1 and gcd(A, c) > 1, "Counterexample coprimalities")
    require((uv + gap) % (c * A) != 0, "Counterexample has no integral h")
    return 4


def check_rectangular_transfer(case):
    """Keep the exact product window as an interval in A*h."""
    X, gap, weights = case["X"], case["gap"], case["weights"]
    windowed, _ = product_coefficients(case)
    rectangle = defaultdict(int)
    for u, v in product(case["alpha"], case["beta"]):
        if (u * v) % case["Q"] == case["a"]:
            rectangle[u * v] += case["alpha"][u] * case["beta"][v]
    bound = (max(rectangle, default=0) + gap) // min(weights)
    checks = 0
    for cutoff in (Fraction(0), Fraction(15, 2), Fraction(X), Fraction(3 * X)):
        for k in range(1, bound + 1):
            for c in divisors(k):
                h = k // c
                lower = max(cutoff, Fraction(X + gap, c))
                upper = Fraction(2 * X + gap, c)
                rectangular_row = sum(
                    weight * rectangle.get(A * k - gap, 0)
                    for A, weight in weights.items() if lower < A * h <= upper
                )
                windowed_row = sum(
                    weight * windowed.get(A * k - gap, 0)
                    for A, weight in weights.items() if A * h > cutoff
                )
                require(rectangular_row == windowed_row, "Rectangular-to-product-window identity")
                checks += 1
    return checks


def check_diagonal_cancellation():
    # G(10)=1 and G(18)=-1, A in {3,5}, g=2. Both nonzero terms have k=4.
    # The signed row vanishes, while its formal diagonal is positive.
    G = {10: 1, 18: -1}
    row = {k: sum(G.get(A * k - 2, 0) for A in (3, 5)) for k in range(1, 8)}
    energy = sum(len(divisors(k)) * value * value for k, value in row.items())
    diagonal = sum(len(divisors(k)) * G.get(A * k - 2, 0) ** 2
                   for A, k in product((3, 5), range(1, 8)))
    require(energy == 0 and diagonal == 6, "Signed square need not dominate diagonal")
    cutoff_row = sum(G.get(A * 4 - 2, 0) for A in (3, 5) if A * 4 > 12)
    require(cutoff_row == -1, "Untwisted zero energy does not control a cutoff")
    return 2


def check_endpoint_phase():
    checks = 0
    auxiliary = (3, 5, 7, 11, 13)
    for D, A, B in product(range(1, 13), auxiliary, auxiliary):
        # For a unit multiplicative phase chi, conj(chi(DB))*chi(DA)
        # equals conj(chi(B))*chi(A). Liouville gives exact integer data.
        require(liouville(D * B) * liouville(D * A) == liouville(B) * liouville(A),
                "Common auxiliary phase cancellation")
        checks += 1
    return checks


def main():
    cases = [
        {"X": 40, "gap": 2, "Q": 1, "a": 0,
         "weights": {3: 1, 5: -1, 7: 2, 11: 1},
         "alpha": {u: (-1 if u % 3 == 0 else 1) for u in range(2, 21)},
         "beta": {v: (v % 5) - 2 for v in range(3, 36)}},
        {"X": 40, "gap": 2, "Q": 5, "a": 2,
         "weights": {3: 1, 5: -1, 7: 1, 11: 2, 13: -1},
         "alpha": {u: 1 for u in range(2, 21)},
         "beta": {v: 1 for v in range(3, 36)}},
        {"X": 72, "gap": 6, "Q": 7, "a": 2,
         "weights": {5: 1, 7: -1, 11: 2, 13: -1},
         "alpha": {u: liouville(u) for u in range(2, 25)},
         "beta": {v: ((v + 1) % 7) - 3 for v in range(2, 61)}},
    ]
    checks = overlaps = 0
    for case in cases:
        count, overlap = check_case(case)
        checks += count + check_rectangular_transfer(case)
        overlaps += overlap
    require(overlaps > 0, "Tests must include (A,c)>1 in actual retained terms")
    checks += 1 + check_adapter_exception() + check_diagonal_cancellation()
    checks += check_endpoint_phase()
    print(f"PASS: {checks} exact finite checks; {overlaps} retained terms with gcd(A,c)>1.")
    print("Scope: grouping, moving cutoffs, diagonal expansion, and unit-phase algebra only.")
    print("No asymptotic cancellation estimate or prime-gap theorem is certified.")


if __name__ == "__main__":
    main()
