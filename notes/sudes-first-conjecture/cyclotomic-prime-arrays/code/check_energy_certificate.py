#!/usr/bin/env python3
"""Independent exact checker for finite trace-energy cyclotomic array certificates.

Standard library only; imports no producer, search, or other project module.
This checker proves the finite pool is complete in the class-number-one fields
certified by its input.  It does not assert a general class-number-one theorem,
nor infer eventual existence from finite examples.  No floating-point value
decides a norm, prime ideal, normalization boundary, or ellipsoid membership.

The exhaustive ellipsoid scan uses rational LDL decomposition, unlike a bounded
coefficient scan.  Each ideal has an energy-minimizing representative as soon
as any one of its generators occurs in that ellipsoid.  All lower-energy and
equal-energy competitors then occur in the same exhaustive scan.  Expected
prime-ideal counts independently certify that no contributing ideal is absent.
"""

from __future__ import annotations

import argparse
import copy
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, product
import json
from math import factorial, gcd, isqrt
from pathlib import Path
import sys


class InvalidCertificate(ValueError):
    """A claimed finite certificate fails an independently checked obligation."""


def require(condition, message):
    if not condition:
        raise InvalidCertificate(message)


def integer(value, name, minimum=None):
    require(type(value) is int, f"{name}: expected an integer")
    if minimum is not None:
        require(value >= minimum, f"{name}: expected >= {minimum}")
    return value


def trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return tuple(a or [0])


def monic_divide(a, b):
    """Exact polynomial division over Z; b is monic."""
    a, b = list(trim(a)), trim(b)
    require(b[-1] == 1, "internal polynomial divisor is not monic")
    q = [0] * max(1, len(a) - len(b) + 1)
    while len(a) >= len(b):
        t, k = a[-1], len(a) - len(b)
        q[k] = t
        for j, x in enumerate(b):
            a[k + j] -= t * x
        while a and a[-1] == 0:
            a.pop()
    require(not any(a), "cyclotomic division had a nonzero remainder")
    return trim(q)


@lru_cache(maxsize=None)
def cyclotomic(c):
    a = [-1] + [0] * (c - 1) + [1]
    for d in range(1, c):
        if c % d == 0:
            a = monic_divide(a, cyclotomic(d))
    return tuple(a)


@lru_cache(maxsize=None)
def prime_divisors(n):
    factors = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            factors.append(p)
            while n % p == 0:
                n //= p
        p += 1 if p == 2 else 2
    if n > 1:
        factors.append(n)
    return tuple(factors)


def phi(n):
    result = n
    for p in prime_divisors(n):
        result = result // p * (p - 1)
    return result


def mobius(n):
    result = 1
    for p in prime_divisors(n):
        if n % (p * p) == 0:
            return 0
        result = -result
    return result


def ramanujan(c, k):
    d = c // gcd(c, k)
    return mobius(d) * (phi(c) // phi(d))


def primes_through(n):
    sieve = bytearray(b"\x01") * (n + 1)
    if n >= 0:
        sieve[0] = 0
    if n >= 1:
        sieve[1] = 0
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p * p:n + 1:p] = b"\x00" * ((n - p * p) // p + 1)
    return [p for p in range(2, n + 1) if sieve[p]]


def order_mod(p, u):
    if u == 1:
        return 1
    require(gcd(p, u) == 1, "multiplicative order requested for a nonunit")
    value = p % u
    f = 1
    while value != 1:
        value = value * p % u
        f += 1
    return f


def expected_ideal_counts(c, bound, omit_ramified):
    """Counts every prime ideal of norm <= bound, including residue degree >1."""
    r = phi(c)
    result = {}
    for p in primes_through(bound):
        if omit_ramified and c % p == 0:
            continue
        u, pa = c, 1
        while u % p == 0:
            u //= p
            pa *= p
        e = phi(pa)
        f = order_mod(p, u)
        if p ** f <= bound:
            require(r % (e * f) == 0, "invalid cyclotomic splitting degree")
            result[p] = r // (e * f)
    return result


def determinant(matrix):
    """Fraction-free determinant with pivoting, independent of resultant code."""
    a = [list(row) for row in matrix]
    n = len(a)
    if n == 0:
        return 1
    sign, previous = 1, 1
    for k in range(n - 1):
        if a[k][k] == 0:
            pivot = next((i for i in range(k + 1, n) if a[i][k]), None)
            if pivot is None:
                return 0
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        diagonal = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = a[i][j] * diagonal - a[i][k] * a[k][j]
                require(numerator % previous == 0, "nonintegral Bareiss step")
                a[i][j] = numerator // previous
        for i in range(k + 1, n):
            a[i][k] = 0
        previous = diagonal
    return sign * a[-1][-1]


def fp_mod(a, b, p):
    a = list(trim([x % p for x in a]))
    b = trim([x % p for x in b])
    require(b != (0,), "zero polynomial divisor")
    inv = pow(b[-1], -1, p)
    while a != [0] and len(a) >= len(b):
        k, factor = len(a) - len(b), a[-1] * inv % p
        for j, x in enumerate(b):
            a[k + j] = (a[k + j] - factor * x) % p
        a = list(trim(a))
    return tuple(a)


def fp_gcd(a, b, p):
    a, b = trim([x % p for x in a]), trim([x % p for x in b])
    while b != (0,):
        a, b = b, fp_mod(a, b, p)
    if a == (0,):
        return a
    inv = pow(a[-1], -1, p)
    return tuple(x * inv % p for x in a)


def fp_product(a, b, g, p):
    result = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] = (result[i + j] + x * y) % p
    return fp_mod(result, g, p)


def fp_power(a, exponent, g, p):
    result = (1,)
    a = fp_mod(a, g, p)
    while exponent:
        if exponent & 1:
            result = fp_product(result, a, g, p)
        exponent >>= 1
        if exponent:
            a = fp_product(a, a, g, p)
    return result


def fp_subtract(a, b, p):
    length = max(len(a), len(b))
    return trim([((a[i] if i < len(a) else 0) -
                  (b[i] if i < len(b) else 0)) % p for i in range(length)])


@lru_cache(maxsize=None)
def irreducible(g, p):
    f = len(g) - 1
    if f <= 0 or g[-1] != 1:
        return False
    x = fp_mod((0, 1), g, p)
    frobenius = [x]
    for _ in range(f):
        frobenius.append(fp_power(frobenius[-1], p, g, p))
    if frobenius[f] != x:
        return False
    return all(fp_gcd(fp_subtract(frobenius[f // q], x, p), g, p) == (1,)
               for q in prime_divisors(f))


@lru_cache(maxsize=None)
def prime_power(n):
    """Return (rational prime, exponent), with exact trial division."""
    if n < 2:
        return None
    p = 2
    while p * p <= n and n % p:
        p += 1 if p == 2 else 2
    if p * p > n:
        return n, 1
    f = 0
    while n % p == 0:
        n //= p
        f += 1
    return (p, f) if n == 1 else None


def floor_fraction(x):
    return x.numerator // x.denominator


def ceil_fraction(x):
    return -((-x.numerator) // x.denominator)


def ceil_sqrt_fraction(x):
    require(x >= 0, "negative rational square root")
    k = isqrt(x.numerator // x.denominator)
    return k if k * k * x.denominator == x.numerator else k + 1


@lru_cache(maxsize=None)
def pi_interval(terms):
    def arctan_inverse(q):
        total = Fraction(0)
        for k in range(terms):
            total += Fraction((-1) ** k, (2 * k + 1) * q ** (2 * k + 1))
        next_term = Fraction((-1) ** terms,
                             (2 * terms + 1) * q ** (2 * terms + 1))
        return min(total, total + next_term), max(total, total + next_term)
    a, b = arctan_inverse(5), arctan_inverse(239)
    lo, hi = 16 * a[0] - 4 * b[1], 16 * a[1] - 4 * b[0]
    denominator = 1 << (3 * terms)
    return (Fraction(floor_fraction(lo * denominator), denominator),
            Fraction(ceil_fraction(hi * denominator), denominator))


@lru_cache(maxsize=None)
def sine_interval(conductor, exponent, terms):
    exponent %= conductor
    if 2 * exponent > conductor:
        exponent -= conductor
    if exponent == 0 or 2 * abs(exponent) == conductor:
        return Fraction(0), Fraction(0)
    pi_lo, pi_hi = pi_interval(terms)
    factor = Fraction(2 * exponent, conductor)
    lo, hi = sorted((factor * pi_lo, factor * pi_hi))
    midpoint, uncertainty = (lo + hi) / 2, (hi - lo) / 2
    total, term = Fraction(0), midpoint
    for k in range(terms):
        total += term
        term *= -midpoint * midpoint / ((2 * k + 2) * (2 * k + 3))
    remainder = abs(midpoint) ** (2 * terms + 1) / factorial(2 * terms + 1)
    error = remainder + uncertainty  # |sin x - sin y| <= |x-y|.
    return total - error, total + error


class ExactField:
    def __init__(self, c):
        self.c = c
        self.polynomial = cyclotomic(c)
        self.r = len(self.polynomial) - 1
        self.w = c if c % 2 == 0 else 2 * c
        self.gram = tuple(tuple(Fraction(ramanujan(c, i - j), 2)
                                for j in range(self.r)) for i in range(self.r))
        self.lower, self.diagonal = self.ldl()
        # Sector boundary arithmetic takes place in Q(zeta_(2w)).
        self.angle_conductor = 2 * self.w
        self.angle_polynomial = cyclotomic(self.angle_conductor)
        self.angle_rank = len(self.angle_polynomial) - 1
        step = self.angle_conductor // c
        self.boundary_vectors = {}
        for shift in (-1, 1):
            vectors = []
            for i in range(self.r):
                k = (step * i + shift) % self.angle_conductor
                a = [0] * self.angle_conductor
                a[k] += 1
                a[(-k) % self.angle_conductor] -= 1
                vectors.append(self.reduce(a, self.angle_polynomial))
            self.boundary_vectors[shift] = tuple(vectors)

    @staticmethod
    def reduce(a, polynomial):
        r = len(polynomial) - 1
        a = list(a) + [0] * max(0, r - len(a))
        for k in range(len(a) - 1, r - 1, -1):
            if a[k]:
                coefficient = a[k]
                for j in range(r):
                    a[k - r + j] -= coefficient * polynomial[j]
        return tuple(a[:r])

    def element(self, a, name="element"):
        require(isinstance(a, list) and len(a) == self.r,
                f"{name}: wrong coefficient-list length")
        require(all(type(x) is int for x in a), f"{name}: nonintegral coefficient")
        return tuple(a)

    def multiply(self, a, b):
        product_coefficients = [0] * (2 * self.r - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                product_coefficients[i + j] += x * y
        return self.reduce(product_coefficients, self.polynomial)

    @lru_cache(maxsize=None)
    def norm(self, a):
        columns = [self.reduce([0] * j + list(a), self.polynomial)
                   for j in range(self.r)]
        return determinant(list(zip(*columns)))

    def energy(self, a):
        value = sum(a[i] * a[j] * self.gram[i][j]
                    for i in range(self.r) for j in range(self.r))
        require(value.denominator == 1, "nonintegral trace energy")
        return value.numerator

    def ldl(self):
        n = self.r
        lower = [[Fraction(i == j) for j in range(n)] for i in range(n)]
        diagonal = []
        for j in range(n):
            diagonal.append(self.gram[j][j] -
                            sum(lower[j][k] ** 2 * diagonal[k] for k in range(j)))
            require(diagonal[-1] > 0, "trace energy is not positive definite")
            for i in range(j + 1, n):
                lower[i][j] = (self.gram[i][j] -
                               sum(lower[i][k] * lower[j][k] * diagonal[k]
                                   for k in range(j))) / diagonal[j]
        return tuple(map(tuple, lower)), tuple(diagonal)

    def ellipsoid(self, bound):
        coordinates = [0] * self.r
        def recurse(i, remaining):
            if i < 0:
                yield tuple(coordinates)
                return
            center = sum(self.lower[j][i] * coordinates[j]
                         for j in range(i + 1, self.r))
            squared_radius = remaining / self.diagonal[i]
            radius = ceil_sqrt_fraction(squared_radius)
            for value in range(ceil_fraction(-center - radius),
                               floor_fraction(-center + radius) + 1):
                term = (value + center) ** 2 * self.diagonal[i]
                if term <= remaining:
                    coordinates[i] = value
                    yield from recurse(i - 1, remaining - term)
        yield from recurse(self.r - 1, Fraction(bound))

    def boundary_sign(self, a, shift):
        vectors = self.boundary_vectors[shift]
        if all(sum(a[i] * vectors[i][j] for i in range(self.r)) == 0
               for j in range(self.angle_rank)):
            return 0
        terms = 8
        step = self.angle_conductor // self.c
        while True:
            lo = hi = Fraction(0)
            for i, coefficient in enumerate(a):
                if coefficient:
                    left, right = sine_interval(self.angle_conductor,
                                                step * i + shift, terms)
                    if coefficient < 0:
                        left, right = right, left
                    lo += coefficient * left
                    hi += coefficient * right
            if lo > 0:
                return 1
            if hi < 0:
                return -1
            terms *= 2  # Terminates because algebraic zero was already excluded.

    @lru_cache(maxsize=None)
    def in_sector(self, a):
        return self.boundary_sign(a, 1) >= 0 and self.boundary_sign(a, -1) < 0

    @lru_cache(maxsize=None)
    def prime_certificate(self, a):
        norm = self.norm(a)
        pp = prime_power(norm)
        if pp is None:
            return None
        p, f = pp
        g = fp_gcd(self.polynomial, a, p)
        if len(g) - 1 != f or not irreducible(g, p):
            return None
        # O/(p,g) is the field F_(p^f), alpha lies in (p,g), and the
        # two ideals have the same norm.  Therefore (alpha)=(p,g).
        return p, f, g

    def discriminant(self):
        derivative = tuple(i * self.polynomial[i] for i in range(1, self.r + 1))
        return abs(self.norm(derivative))


@lru_cache(maxsize=None)
def field(c):
    return ExactField(c)


def ideal_key(prime_data):
    return prime_data[0], prime_data[2]


@lru_cache(maxsize=None)
def canonical_scan(c, energy_bound, norm_bound):
    k = field(c)
    representatives = {}
    visited = 0
    for a in k.ellipsoid(energy_bound):
        visited += 1
        norm = k.norm(a)
        if norm < 2 or norm > norm_bound:
            continue
        certificate = k.prime_certificate(a)
        if certificate is None or not k.in_sector(a):
            continue
        key = ideal_key(certificate)
        record = (k.energy(a), a)
        if key not in representatives or record < representatives[key]:
            representatives[key] = record
    return tuple((key, value[1]) for key, value in sorted(representatives.items())), visited


def minkowski_check(k, certificate):
    require(certificate.get("method") == "minkowski-all-small-primes",
            "unsupported class-number certificate")
    discriminant = k.discriminant()
    require(certificate.get("discriminant") == discriminant,
            "incorrect absolute discriminant")
    root = isqrt(discriminant)
    if root * root < discriminant:
        root += 1
    # pi>3 gives a strict rational upper bound for Minkowski's real bound.
    upper = Fraction(4, 3) ** (k.r // 2) * Fraction(factorial(k.r), k.r ** k.r) * root
    bound = floor_fraction(upper)
    require(certificate.get("bound_floor") == bound, "incorrect Minkowski bound floor")
    generators = certificate.get("prime_generators")
    require(isinstance(generators, list), "missing small-prime generators")
    keys, counts = set(), Counter()
    for index, value in enumerate(generators):
        a = k.element(value, f"small-prime generator {index}")
        prime_data = k.prime_certificate(a)
        require(prime_data is not None, "small-prime generator is not a prime element")
        require(k.norm(a) <= bound, "small-prime generator exceeds Minkowski bound")
        key = ideal_key(prime_data)
        require(key not in keys, "repeated small prime ideal")
        keys.add(key)
        counts[prime_data[0]] += 1
    expected = expected_ideal_counts(k.c, bound, omit_ramified=False)
    require(dict(counts) == expected, "small-prime generators do not cover every required ideal")
    return bound


def required_lines(dimension, side):
    """Enumerate all signed-coordinate lines from subsets, fixing reversal."""
    result = set()
    for varying_count in range(1, dimension + 1):
        for varying in combinations(range(dimension), varying_count):
            fixed = [j for j in range(dimension) if j not in varying]
            for fixed_values in product(range(side), repeat=len(fixed)):
                for other_signs in product((1, -1), repeat=varying_count - 1):
                    signs = (1,) + other_signs
                    cells = []
                    for t in range(side):
                        position = [0] * dimension
                        for j, value in zip(fixed, fixed_values):
                            position[j] = value
                        for j, sign in zip(varying, signs):
                            position[j] = t if sign == 1 else side - 1 - t
                        flattened = 0
                        for value in position:
                            flattened = flattened * side + value
                        cells.append(flattened)
                    result.add(tuple(sorted(cells)))
    expected = (1 if side == 1 else 2 * side + 2 if dimension == 2
                else 3 * side * side + 6 * side + 4)
    require(len(result) == expected, "internal line enumeration count failed")
    return result


def check_certificate(data):
    require(isinstance(data, dict), "certificate is not a JSON object")
    require(data.get("format") == "cyclotomic-energy-array-v1", "wrong certificate format")
    c = integer(data.get("conductor"), "conductor", 3)
    require(c % 4 != 2, "conductor has not been reduced")
    require(c not in (5, 8, 12), "these conductors retain their distinct balanced-log pool")
    k = field(c)
    require(data.get("polynomial") == list(k.polynomial), "incorrect cyclotomic polynomial")
    require(data.get("normalization") == "trace-energy-sector-lex-v1", "wrong normalization")
    require(data.get("omitted_rational_primes") == list(prime_divisors(c)),
            "ramified-prime exclusions changed")
    dimension = integer(data.get("dimension"), "dimension")
    require(dimension in (2, 3), "dimension must be 2 or 3")
    side = integer(data.get("side"), "side", 1)
    size = side ** dimension
    completeness = data.get("pool_completeness")
    require(isinstance(completeness, dict), "missing completeness certificate")
    class_certificate = completeness.get("class_number_certificate")
    require(isinstance(class_certificate, dict), "missing class-number certificate")
    small_bound = minkowski_check(k, class_certificate)
    energy_bound = integer(completeness.get("energy_bound"), "energy bound", 1)
    cutoff = integer(completeness.get("norm_cutoff"), "norm cutoff", 2)
    scan, visited = canonical_scan(c, energy_bound, max(cutoff, small_bound))
    canonical = {key: a for key, a in scan if c % key[0] != 0 and k.norm(a) <= cutoff}
    counts = Counter(key[0] for key in canonical)
    expected = expected_ideal_counts(c, cutoff, omit_ramified=True)
    require(dict(counts) == expected,
            "energy scan misses a prime ideal through the cutoff (including norm ties)")
    complete_pool = sorted(canonical.values(), key=lambda a: (k.norm(a), a))
    declared_complete = completeness.get("all_through_cutoff")
    require(isinstance(declared_complete, list), "missing complete cutoff list")
    declared_complete = [k.element(a, "complete cutoff entry") for a in declared_complete]
    require(declared_complete == complete_pool, "incorrect energy-minimal complete cutoff list")
    require(len(complete_pool) >= size, "too few initial prime elements")
    pool_data = data.get("pool")
    require(isinstance(pool_data, list), "missing pool")
    pool = [k.element(a, "pool entry") for a in pool_data]
    require(pool == complete_pool[:size], "pool is not the exact initial canonical prefix")
    require(k.norm(pool[-1]) == cutoff, "cutoff is not the final prefix norm")
    arrangement_data = data.get("arrangement")
    require(isinstance(arrangement_data, list), "missing arrangement")
    arrangement = [k.element(a, "array entry") for a in arrangement_data]
    require(len(arrangement) == size and Counter(arrangement) == Counter(pool),
            "array does not use each whole pool element exactly once")
    wanted_lines = required_lines(dimension, side)
    lines = data.get("lines")
    require(isinstance(lines, list), "missing line certificates")
    seen = set()
    residue_degrees = Counter()
    for record in lines:
        require(isinstance(record, dict), "malformed line record")
        cells = record.get("cells")
        require(isinstance(cells, list) and len(cells) == side and
                all(type(j) is int and 0 <= j < size for j in cells), "invalid line cells")
        key = tuple(sorted(cells))
        require(key in wanted_lines and key not in seen, "wrong or repeated line")
        seen.add(key)
        total = tuple(sum(arrangement[j][i] for j in cells) for i in range(k.r))
        require(record.get("sum") == list(total), "incorrect exact line sum")
        norm = k.norm(total)
        require(record.get("norm") == norm, "incorrect line norm")
        prime_data = k.prime_certificate(total)
        require(prime_data is not None, "line sum is zero, a unit, or a nonprime element")
        p, f, factor = prime_data
        require(record.get("p") == p and record.get("residue_degree") == f,
                "incorrect line residue characteristic or degree")
        require(record.get("factor") == list(factor), "incorrect line prime-ideal factor")
        residue_degrees[f] += 1
    require(seen == wanted_lines, "missing required diagonal or axis line")
    digest_data = {"pool": pool, "arrangement": arrangement,
                   "lines": sorted(wanted_lines)}
    digest = sha256(json.dumps(digest_data, separators=(",", ":")).encode()).hexdigest()
    return {"conductor": c, "rank": k.r, "dimension": dimension, "side": side,
            "pool_size": size, "cutoff": cutoff, "all_cutoff_ideals": len(complete_pool),
            "energy_bound": energy_bound, "ellipsoid_points": visited,
            "minkowski_bound_floor": small_bound, "lines": len(wanted_lines),
            "line_residue_degrees": dict(residue_degrees), "fixture_sha256": digest}


def negative_controls(data):
    mutations = []
    def add(name, mutate):
        altered = copy.deepcopy(data)
        mutate(altered)
        mutations.append((name, altered))
    add("insufficient_energy_bound", lambda d: d["pool_completeness"].__setitem__("energy_bound", 1))
    add("omitted_prime_class_or_norm_tie", lambda d: d["pool_completeness"]["all_through_cutoff"].pop())
    add("wrong_polynomial", lambda d: d["polynomial"].__setitem__(0, d["polynomial"][0] + 1))
    add("wrong_discriminant", lambda d: d["pool_completeness"]["class_number_certificate"].__setitem__("discriminant", 1))
    add("wrong_minkowski_bound", lambda d: d["pool_completeness"]["class_number_certificate"].__setitem__("bound_floor", 0))
    add("hidden_unit_rescaling", lambda d: d["arrangement"].__setitem__(0, [-x for x in d["arrangement"][0]]))
    add("missing_line", lambda d: d["lines"].pop())
    add("wrong_line_norm", lambda d: d["lines"][0].__setitem__("norm", 1))
    add("wrong_residue_degree", lambda d: d["lines"][0].__setitem__("residue_degree", 0))
    add("wrong_residue_characteristic", lambda d: d["lines"][0].__setitem__("p", 1))
    add("wrong_prime_factor", lambda d: d["lines"][0].__setitem__("factor", [1]))
    if data["pool_completeness"]["class_number_certificate"]["prime_generators"]:
        add("omitted_minkowski_prime_ideal", lambda d: d["pool_completeness"]["class_number_certificate"]["prime_generators"].pop())
    # Replace the same ideal everywhere by a sector-normalized associate of
    # larger energy.  The rejection must come from the independent energy
    # minimum, not merely a mismatch between declared pool and array entries.
    k = field(data["conductor"])
    original = tuple(data["pool"][0])
    if k.r > 2:
        length = next(j for j in range(2, k.c) if gcd(j, k.c) == 1)
        unit = k.reduce([1] * length, k.polynomial)
        require(k.norm(unit) == 1, "internal cyclotomic-unit control failed")
        associate = original
        replacement = None
        for _ in range(20):
            associate = k.multiply(associate, unit)
            if k.energy(associate) <= k.energy(original):
                continue
            for sign in (1, -1):
                for power in range(k.c):
                    candidate = k.reduce([0] * power + [sign * x for x in associate],
                                         k.polynomial)
                    if k.in_sector(candidate):
                        replacement = candidate
                        break
                if replacement is not None:
                    break
            if replacement is not None:
                break
        require(replacement is not None, "could not build a nonminimal-associate control")
        require(ideal_key(k.prime_certificate(replacement)) ==
                ideal_key(k.prime_certificate(original)), "control changed its prime ideal")
        def replace_associate(d):
            for key in ("pool", "arrangement"):
                d[key] = [list(replacement) if tuple(a) == original else a for a in d[key]]
            block = d["pool_completeness"]
            block["all_through_cutoff"] = [list(replacement) if tuple(a) == original else a
                                           for a in block["all_through_cutoff"]]
        add("coherent_nonminimal_unit_associate", replace_associate)
    if len(data["pool"]) > 1:
        add("repeated_entry", lambda d: d["arrangement"].__setitem__(0, d["arrangement"][1]))
        add("wrong_prefix_order", lambda d: d["pool"].__setitem__(slice(0, 2), d["pool"][:2][::-1]))
    rejected = []
    for name, altered in mutations:
        try:
            check_certificate(altered)
        except InvalidCertificate:
            rejected.append(name)
        else:
            raise InvalidCertificate(f"negative control was accepted: {name}")
    return rejected


def arithmetic_controls():
    """Finite controls for conventions that a favorable array may not expose."""
    checks = 0
    for c in (3, 4, 7, 9, 15, 16):
        k = field(c)
        zero, one = (0,) * k.r, (1,) + (0,) * (k.r - 1)
        require(k.norm(zero) == 0 and k.prime_certificate(zero) is None,
                "zero was accepted as a prime element")
        require(k.norm(one) == 1 and k.prime_certificate(one) is None,
                "a unit was accepted as a prime element")
        require(k.in_sector(one) and not k.in_sector(tuple(-x for x in one)),
                "root-of-unity sector convention failed")
        checks += 3
        b = (c - 1) // 2 if c % 2 else c // 2 - 1
        lower_coefficients = [0] * (b + 1)
        lower_coefficients[0], lower_coefficients[b] = 1, -1
        lower = k.reduce(lower_coefficients, k.polynomial)
        upper_coefficients = [0] * (c - b + 1)
        upper_coefficients[0], upper_coefficients[c - b] = 1, -1
        upper = k.reduce(upper_coefficients, k.polynomial)
        require(k.boundary_sign(lower, 1) == 0 and k.in_sector(lower),
                "exact lower sector boundary was not included")
        require(k.boundary_sign(upper, -1) == 0 and not k.in_sector(upper),
                "exact upper sector boundary was not excluded")
        checks += 2
        for offset in (1, -1):
            near_boundary = [10 ** 12 * x for x in lower]
            near_boundary[0] += offset
            require(k.in_sector(tuple(near_boundary)) == (offset == 1),
                    "certified near-boundary sign failed")
            checks += 1
    for c, p, expected_prime in ((3, 2, True), (7, 3, True), (9, 2, True),
                                  (7, 2, False), (15, 2, False), (16, 2, False)):
        k = field(c)
        a = (p,) + (0,) * (k.r - 1)
        require(k.norm(a) == p ** k.r, "rational prime norm control failed")
        prime_data = k.prime_certificate(a)
        require((prime_data is not None) == expected_prime,
                "prime power norm was confused with a prime element")
        if expected_prime:
            require(prime_data[1] == k.r, "inert prime residue degree was lost")
        checks += 1
    k = field(16)
    ramified = (1, -1) + (0,) * (k.r - 2)
    require(k.norm(ramified) == 2 and k.prime_certificate(ramified) is not None,
            "ramified prime-element control failed")
    require(k.prime_certificate(k.multiply(ramified, ramified)) is None,
            "a squared ramified prime was accepted")
    checks += 2
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--negative-controls", action="store_true")
    parser.add_argument("certificates", nargs="+", type=Path)
    args = parser.parse_args()
    total_controls = 0
    if args.negative_controls:
        print(json.dumps({"arithmetic_controls": arithmetic_controls(), "status": "verified"},
                         sort_keys=True))
    for path in args.certificates:
        try:
            data = json.loads(path.read_text())
            result = check_certificate(data)
            if args.negative_controls:
                controls = negative_controls(data)
                total_controls += len(controls)
                result["rejected_negative_controls"] = controls
            result["file"] = path.name
            result["status"] = "verified"
            print(json.dumps(result, sort_keys=True))
        except (InvalidCertificate, KeyError, TypeError, json.JSONDecodeError) as error:
            print(json.dumps({"file": str(path), "status": "rejected", "reason": str(error)}))
            return 1
    print(json.dumps({"status": "verified", "certificates": len(args.certificates),
                      "negative_controls_rejected": total_controls}, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
