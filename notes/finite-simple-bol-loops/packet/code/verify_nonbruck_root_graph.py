#!/usr/bin/env python3
"""Check root-graph parameter orbits for F4/F8/F16 and count arithmetic."""

from fractions import Fraction
from itertools import combinations, product
from math import gcd


def field_multiply(a, b, f, polynomial):
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & (1 << f):
            a ^= polynomial
    return result


def field_power(a, exponent, f, polynomial):
    result = 1
    while exponent:
        if exponent & 1:
            result = field_multiply(result, a, f, polynomial)
        a = field_multiply(a, a, f, polynomial)
        exponent >>= 1
    return result


def apply_linear(columns, x):
    result = 0
    for i, column in enumerate(columns):
        if x & (1 << i):
            result ^= column
    return result


def transform(columns, c, d, j, f, polynomial):
    def multiply(a, b):
        return field_multiply(a, b, f, polynomial)

    def power(a, exponent):
        return field_power(a, exponent, f, polynomial)

    def image(x):
        inverse_frobenius = power(x, 1 << ((f - j) % f))
        inside = apply_linear(columns, multiply(d, inverse_frobenius))
        return multiply(c, power(inside, 1 << j))

    return tuple(image(1 << i) for i in range(f))


def orbit_sizes(f, polynomial):
    q = 1 << f
    maps = {
        columns
        for columns in product(range(q), repeat=f)
        if any(columns)
    }
    assert len(maps) == (1 << (f * f)) - 1
    remaining = set(maps)
    orbits = []
    while remaining:
        seed = min(remaining)
        orbit = {
            transform(seed, c, d, j, f, polynomial)
            for c in range(1, q)
            for d in range(1, q)
            for j in range(f)
        }
        assert orbit <= remaining
        remaining.difference_update(orbit)
        image_size = len({apply_linear(seed, x) for x in range(q)})
        rank = image_size.bit_length() - 1
        assert image_size == 1 << rank
        assert all(len({apply_linear(item, x) for x in range(q)}) == image_size
                   for item in orbit)
        orbits.append((rank, len(orbit), seed))
    return len(maps), sorted(orbits)


def support_formula(f, p=2):
    """Evaluate the proposed Burnside formula, counting singleton supports."""
    total = 0
    for size in range(1, f + 1):
        for support in combinations(range(f), size):
            if size == 1:
                total += 1
                continue
            h = f
            for i in support[1:]:
                h = gcd(h, i - support[0])
            numerator = sum(
                (p ** gcd(f, j) - 1) ** (size - 2)
                * (p ** gcd(h, j) - 1)
                for j in range(f)
            )
            assert numerator % f == 0
            total += numerator // f
    return total


def divisor_formula(f, p=2):
    """Evaluate the independent divisor-only Burnside expression exactly."""
    divisors = [d for d in range(1, f + 1) if f % d == 0]
    exact_degree = {}
    for h in divisors:
        exact_degree[h] = p ** h - 1 - sum(
            exact_degree[d] for d in exact_degree if h % d == 0
        )
    total = Fraction(0)
    for s in divisors:
        phi = sum(gcd(k, f // s) == 1 for k in range(1, f // s + 1))
        inner = sum(
            h * exact_degree[h] * (p ** (f * s // h) - 1)
            for h in divisors if s % h == 0
        )
        total += Fraction(phi * inner, (p ** s - 1) ** 2)
    result = total / f
    assert result.denominator == 1
    return result.numerator


def main():
    # Binary encodings use the polynomial bases (1,z) and (1,z,z²).
    count4, orbits4 = orbit_sizes(2, 0b111)       # z² + z + 1
    count8, orbits8 = orbit_sizes(3, 0b1011)    # z³ + z + 1
    count16, orbits16 = orbit_sizes(4, 0b10011) # z⁴ + z + 1
    assert count4 == 15 and [(r, n) for r, n, _ in orbits4] == [
        (1, 9), (2, 3), (2, 3)
    ]
    assert count8 == 511 and [(r, n) for r, n, _ in orbits8] == [
        (1, 49), (2, 49), (2, 49), (2, 49), (2, 147),
        (3, 7), (3, 7), (3, 7), (3, 147)
    ]
    totals = [support_formula(f) for f in range(2, 9)]
    assert totals == [divisor_formula(f) for f in range(2, 9)]
    for p in (3, 5, 7):
        assert support_formula(2, p) == divisor_formula(2, p) == p + 1
    for p in (5, 7, 11):
        assert support_formula(1, p) == divisor_formula(1, p) == 1
    assert totals[:3] == [3, 9, 91]
    assert count16 == 65535 and len(orbits16) == 91
    assert totals[:3] == [len(orbits4), len(orbits8), len(orbits16)]
    print(f"Matching binary Burnside totals for f=2,...,8: {totals}")
    print("Odd characteristic arithmetic: f=1 -> 1; f=2 -> p+1 (tested primes).")
    print(f"F16: {count16} maps, {len(orbits16)} orbits")
    print(f"F4: {count4} maps, (rank, size) {[(r, n) for r, n, _ in orbits4]}")
    print(f"F8: {count8} maps, (rank, size) {[(r, n) for r, n, _ in orbits8]}")
    print("Parameter orbits and formula arithmetic checked; no loop axioms or isomorphisms tested.")


if __name__ == "__main__":
    main()
