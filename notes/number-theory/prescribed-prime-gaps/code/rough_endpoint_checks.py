#!/usr/bin/env python3
"""Finite exact checks for rough-endpoint-marking.md.

These checks certify finite algebra and accounting identities only. They do not
verify Bombieri--Vinogradov, any asymptotic estimate, or a prime-pair lower bound.
Primality/factorization uses exact integer trial division. All validity checks
use explicit exceptions, so the checks remain active under python -O.
"""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from math import comb, gcd, prod


def require(condition: bool, description: str) -> None:
    if not condition:
        raise RuntimeError(description)


@lru_cache(maxsize=None)
def factor(n: int) -> tuple[tuple[int, int], ...]:
    if n < 1:
        raise ValueError("factor requires a positive integer")
    result: list[tuple[int, int]] = []
    q = 2
    while q * q <= n:
        exponent = 0
        while n % q == 0:
            n //= q
            exponent += 1
        if exponent:
            result.append((q, exponent))
        q = 3 if q == 2 else q + 2
    if n > 1:
        result.append((n, 1))
    return tuple(result)


def mu(n: int) -> int:
    factors = factor(n)
    if any(exponent > 1 for _, exponent in factors):
        return 0
    return -1 if len(factors) % 2 else 1


def phi(n: int) -> int:
    return prod((p - 1) * p ** (exponent - 1) for p, exponent in factor(n))


@lru_cache(maxsize=None)
def divisors(n: int) -> tuple[int, ...]:
    result = [1]
    for p, exponent in factor(n):
        result = [d * p**j for d in result for j in range(exponent + 1)]
    return tuple(sorted(result))


def add_log(vector: dict[int, int], n: int, scale: int = 1) -> None:
    for p, exponent in factor(n):
        vector[p] += scale * exponent


def normalized(vector: dict[int, int]) -> dict[int, int]:
    return {p: coefficient for p, coefficient in vector.items() if coefficient}


def lambda_vector(n: int) -> dict[int, int]:
    factors = factor(n)
    return {factors[0][0]: 1} if len(factors) == 1 else {}


def is_prime(n: int) -> bool:
    return n >= 2 and factor(n) == ((n, 1),)


def prime_vector_sum(c: int, g: int, values: list[int]) -> dict[int, int]:
    vector: dict[int, int] = defaultdict(int)
    for d in values:
        p = c * d - g
        if is_prime(p):
            vector[p] += mu(d)
    return normalized(vector)


def run() -> dict[str, int]:
    counts: dict[str, int] = defaultdict(int)

    for omega in range(101):
        for k in range(31):
            bk = sum((-1)**j * comb(omega, j) for j in range(min(k, omega) + 1))
            remainder = comb(omega, k + 1) if k + 1 <= omega else 0
            require(abs(int(omega == 0) - bk) <= remainder,
                    f"Bonferroni remainder failed: omega={omega}, k={k}")
            counts["bonferroni"] += 1

    prime_sets = ((2,), (2, 3), (3, 5, 7), (2, 5, 11))
    for n in range(1, 5001):
        n_divisors = divisors(n)
        square_sum = sum(mu(s) for s in n_divisors if n % (s * s) == 0)
        require(square_sum == mu(n)**2, f"squarefree expansion failed: n={n}")
        counts["squarefree"] += 1

        for selected in prime_sets:
            w = prod(selected)
            lhs: dict[int, int] = defaultdict(int)
            for d in n_divisors:
                if gcd(d, w) == 1:
                    add_log(lhs, n // d, mu(d))
            b = n
            for p in selected:
                while b % p == 0:
                    b //= p
            rhs = dict(factor(n)) if b == 1 else lambda_vector(b)
            require(normalized(lhs) == rhs,
                    f"depleted convolution failed: n={n}, W={selected}")
            counts["depleted_convolution"] += 1

        for a in n_divisors:
            if not mu(a):
                continue
            lhs = defaultdict(int)
            for d in n_divisors:
                if d % a == 0:
                    add_log(lhs, n // d, mu(d))
            m = n // a
            m0 = m
            for p, _ in factor(a):
                while m0 % p == 0:
                    m0 //= p
            rhs_vector: dict[int, int] = defaultdict(int)
            for p, coefficient in lambda_vector(m0).items():
                rhs_vector[p] += mu(a) * coefficient
            if m0 == 1:
                add_log(rhs_vector, m, mu(a))
            require(normalized(lhs) == normalized(rhs_vector),
                    f"forced-divisor convolution failed: n={n}, A={a}")
            counts["forced_divisor_convolution"] += 1

        if is_prime(n):
            cutoff = max(1, n // 2)
            remainder_vector: dict[int, int] = defaultdict(int)
            for d in n_divisors:
                if d > cutoff:
                    add_log(remainder_vector, n // d, mu(d))
            require(not normalized(remainder_vector),
                    f"prime-endpoint large remainder not zero: n={n}")
            counts["prime_endpoint_remainder"] += 1

    selected = (3, 5, 7)
    for c in range(1, 201):
        finite_sum = sum(
            (Fraction(mu(s) * phi(c), phi(c * s * s))
             for s in divisors(prod(selected))), Fraction(0)
        )
        euler_product = prod(
            1 - Fraction(phi(c), phi(c * p * p)) for p in selected
        )
        require(finite_sum == euler_product,
                f"squarefree Euler product failed: c={c}")
        for p in selected:
            target = Fraction(1, p * p if c % p == 0 else p * (p - 1))
            require(Fraction(phi(c), phi(c * p * p)) == target,
                    f"local squarefree factor failed: c={c}, p={p}")
            counts["local_squarefree_factor"] += 1
        counts["finite_squarefree_euler_product"] += 1

    selected = (5, 7, 11)
    w = prod(selected)
    q = 6
    seen: dict[int, tuple[int, int]] = {}
    for d in range(1, 201):
        if gcd(d, w) != 1:
            continue
        for r in divisors(w):
            modulus = q * d * r
            require(modulus not in seen or seen[modulus] == (d, r),
                    "W-free/W-supported factorization was not unique")
            seen[modulus] = (d, r)
            counts["unique_modulus_factorization"] += 1

    multiplicities: dict[int, set[tuple[int, int, int]]] = defaultdict(set)
    s_limit = 3
    for c in range(1, 101):
        if gcd(c, w) != 1:
            continue
        for s in range(1, s_limit + 1):
            for r in divisors(w):
                multiplicities[q * c * s * s * r].add((c, s, r))
    for modulus, tuples in multiplicities.items():
        require(len(tuples) <= s_limit,
                f"squarefree modulus multiplicity too large: {modulus}")
        require(len({r for _, _, r in tuples}) == 1,
                "W-supported factor not determined by the modulus")
        counts["bounded_squarefree_multiplicity"] += 1

    for a in range(2, 13):
        for c in (3, 5, 7):
            for g in (2, 4):
                lo, hi = 10, 600
                partitioned: list[int] = []
                for b in range(a):
                    h_lo = (lo + b + a - 1) // a
                    h_hi = (hi + b) // a
                    partitioned.extend(a * h - b for h in range(h_lo, h_hi + 1))
                require(sorted(partitioned) == list(range(lo, hi + 1)),
                        "off-endpoint shifts did not partition residue classes")
                require(
                    prime_vector_sum(c, g, partitioned)
                    == prime_vector_sum(c, g, list(range(lo, hi + 1))),
                    "off-endpoint weighted partition failed",
                )
                counts["off_endpoint_partition"] += 1

    return dict(sorted(counts.items()))


if __name__ == "__main__":
    results = run()
    for name, count in results.items():
        print(f"{name}: {count} exact checks")
    print(f"TOTAL: {sum(results.values())} finite exact checks passed")
    print("Scope: algebra and finite accounting only; no asymptotic or prime-gap claim.")

