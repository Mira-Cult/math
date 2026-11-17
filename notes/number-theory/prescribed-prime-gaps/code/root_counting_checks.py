#!/usr/bin/env python3
"""Exact finite modular checks for root-counting-moduli.md.

No asymptotic estimate, signed correlation, or prime-gap theorem is tested.
All verification branches remain active under Python -O.
"""

from collections import Counter
from fractions import Fraction
from math import gcd


def require(condition, message):
    if not condition:
        raise ValueError(message)


def prime_powers(n):
    result = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            result[p] = result.get(p, 1) * p
            n //= p
        p += 1
    if n > 1:
        result[n] = n
    return result


def phi(n):
    result = n
    for p in prime_powers(n):
        result = result // p * (p - 1)
    return result


def sl2(modulus):
    """Enumerate determinant-one matrices by solving the final congruence."""
    for u in range(modulus):
        q = gcd(u, modulus)
        reduced = modulus // q
        inv = pow(u // q, -1, reduced) if reduced > 1 else 0
        for v in range(modulus):
            if gcd(gcd(u, v), modulus) != 1:
                continue
            for c in range(modulus):
                rhs = 1 + v * c
                if rhs % q:
                    continue
                d0 = (rhs // q * inv) % reduced
                for j in range(q):
                    yield u, c, v, d0 + j * reduced


def check_crt_roots():
    checks = nonsquarefree_cases = 0
    for S in range(1, 15):
        for u in range(2, 19):
            for v in (1, 2, 3, 5):
                if gcd(u, v) != 1:
                    continue
                c = (-pow(v, -1, u)) % u
                d = (1 + v * c) // u
                u0, c0, v0, d0 = (z % S for z in (u, c, v, d))
                require((u0 * d0 - v0 * c0 - 1) % S == 0,
                        "Valid source matrix class")
                N = u * S
                literal = {
                    (cc, vv)
                    for cc in range(c0, N, S)
                    for vv in range(v0, N, S)
                    if (cc * vv - u * d0 + 1) % N == 0
                }
                count = u
                for p in prime_powers(u):
                    if S % p:
                        count = count // p * (p - 1)
                require(len(literal) == count, "Exact R_u cardinality")

                S1 = 1
                for p, power in prime_powers(S).items():
                    if u % p == 0:
                        S1 *= power
                S2 = S // S1
                m = u * S1
                require(gcd(S2, m) == 1, "Full-prime-power CRT factors")
                require(gcd(u * d0 - 1, m) == 1, "Kloosterman multiplier unit")
                gamma = pow(S2, -1, m)
                eta = pow(m, -1, S2) if S2 > 1 else 0
                reconstructed = set()
                for y in range(m):
                    if gcd(y, m) != 1 or (y - c0) % S1:
                        continue
                    z = ((u * d0 - 1) * pow(y, -1, m)) % m
                    cc = (c0 * m * eta + y * S2 * gamma) % N
                    vv = (v0 * m * eta + z * S2 * gamma) % N
                    reconstructed.add((cc, vv))
                    # Exact Fourier phases after additive orthogonality has
                    # selected y == c0 (mod S1). No floating point roots used.
                    for h, k in ((1, 0), (0, -1), (2, 3), (-3, 2)):
                        lhs = (h * cc + k * vv) % N
                        rhs = (m * eta * (h * c0 + k * v0)
                               + S2 * gamma * (h * y + k * z)) % N
                        require(lhs == rhs, "CRT Fourier phase identity")
                        checks += 1
                require(literal == reconstructed, "Exact root-set CRT bijection")
                if any(power != p for p, power in prime_powers(S).items()):
                    nonsquarefree_cases += 1
                checks += 5

    require(gcd(4 // gcd(2, 4), 2 * gcd(2, 4)) != 1,
            "Old gcd split must fail at u=2,S=4")
    return checks + 1, nonsquarefree_cases


def kernel_line(u, c, gap, p):
    # A kernel vector for (u,-gap*c) is (gap*c,u).
    xx, yy = gap * c % p, u % p
    require(xx != 0 or yy != 0, "Nonzero projective kernel vector")
    return xx * pow(yy, -1, p) % p if yy else "infinity"


def check_densities():
    checks = matrices = 0
    for gap, aux in ((2, 1), (4, 1), (8, 1), (9, 1), (12, 1),
                     (2, 5), (4, 5), (6, 5), (8, 5), (12, 5),
                     (4, 7), (2, 15)):
        require(gcd(gap, aux) == 1, "Auxiliary modulus coprime to gap")
        primes = tuple(prime_powers(aux))
        require(all(prime_powers(aux)[p] == p for p in primes),
                "Auxiliary modulus squarefree")
        modulus = gap * aux
        classes = Counter()
        total = 0
        for u, c, v, d in sl2(modulus):
            require((u * d - v * c - 1) % modulus == 0,
                    "Enumerated determinant one")
            total += 1
            if gcd(u * v, gap) == 1:
                ratio = v * pow(u, -1, gap) % gap
                lines = tuple(kernel_line(u, c, gap, p) for p in primes)
                classes[ratio, lines] += 1
        predicted_order = Fraction(modulus ** 3)
        for p in prime_powers(modulus):
            predicted_order *= Fraction(p * p - 1, p * p)
        require(total == predicted_order, "SL2 order at arbitrary modulus")
        expected = gap * phi(gap)
        expected_classes = phi(gap)
        for p in primes:
            expected *= p * (p - 1)
            expected_classes *= p + 1
        require(len(classes) == expected_classes, "All unit ratios and lines occur")
        for count in classes.values():
            require(count == expected, "Exact unit-ratio/projective-line multiplicity")
            checks += 1
        density = Fraction(1, gap)
        for p in prime_powers(gap):
            density *= Fraction(p, p + 1)
        for p in primes:
            density /= p + 1
        require(Fraction(expected, total) == density, "Exact RC9 density")
        matrices += total
        checks += 5
    return checks, matrices


def main():
    first, nonfree = check_crt_roots()
    second, matrices = check_densities()
    print(f"PASS: {first + second} exact checks; {nonfree} nonsquarefree root cases;")
    print(f"      {matrices} determinant-one matrices independently enumerated.")
    print("Scope: modular cardinalities, CRT phases and densities only.")
    print("No asymptotic cancellation or prime-gap theorem is certified.")


if __name__ == "__main__":
    main()
