#!/usr/bin/env python3
"""Exact producer for the new trace-energy canonical cyclotomic model.

Author: /root. This does not change the frozen quartic producer. Arithmetic,
energy ellipsoid enumeration, sector decisions, and accepted primality tests
are exact. Floating point is not used to accept normalization or primality.
The small sample pool driver proves class number one by an explicit Minkowski
certificate; the general mathematical enumeration theorem has no such limit.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import gcd, isqrt, factorial
import itertools


def trim(a):
    a = list(a)
    while a and not a[-1]:
        a.pop()
    return a


def exact_div(a, b):
    a = trim(a); b = trim(b)
    assert b[-1] == 1
    out = [0] * max(0, len(a)-len(b)+1)
    while len(a) >= len(b):
        k = len(a)-len(b); v = a[-1]; out[k] = v
        for j, u in enumerate(b):
            a[k+j] -= v*u
        a = trim(a)
    assert not a
    return out


@lru_cache(None)
def phi_poly(m):
    a = [-1]+[0]*(m-1)+[1]
    for d in range(1, m):
        if m % d == 0:
            a = exact_div(a, phi_poly(d))
    return tuple(a)


def factors(n):
    out = {}; p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0)+1; n //= p
        p += 1 if p == 2 else 2
    if n > 1:
        out[n] = out.get(n, 0)+1
    return out


def phi(n):
    v = n
    for p in factors(n):
        v = v//p*(p-1)
    return v


def mobius(n):
    f = factors(n)
    return 0 if any(e > 1 for e in f.values()) else (-1)**len(f)


def ramanujan(m, k):
    d = m//gcd(m, k)
    return mobius(d)*phi(m)//phi(d)


def det(a):
    a = [list(row) for row in a]
    n = len(a); previous = 1; sign = 1
    for k in range(n-1):
        if not a[k][k]:
            i = next((i for i in range(k+1, n) if a[i][k]), None)
            if i is None:
                return 0
            a[k], a[i] = a[i], a[k]; sign = -sign
        pivot = a[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                v = a[i][j]*pivot-a[i][k]*a[k][j]
                assert v % previous == 0
                a[i][j] = v//previous
            a[i][k] = 0
        previous = pivot
    return sign*a[-1][-1]


@lru_cache(None)
def rational_prime(n):
    """Miller witnesses only reject; positive answers use complete trial division."""
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small:
        if n % p == 0:
            return n == p
    d = n-1; s = 0
    while d % 2 == 0:
        d //= 2; s += 1
    for a in (2, 3, 5, 7):
        x = pow(a, d, n)
        if x in (1, n-1):
            continue
        for _ in range(s-1):
            x = x*x % n
            if x == n-1:
                break
        else:
            return False
    for p in range(41, isqrt(n)+1, 2):
        if n % p == 0:
            return False
    return True


def iroot(n, k):
    lo, hi = 0, 1 << ((n.bit_length()+k-1)//k)
    while lo+1 < hi:
        mid = (lo+hi)//2
        if mid**k <= n:
            lo = mid
        else:
            hi = mid
    return hi if hi**k <= n else lo


def prime_power(n, r):
    if rational_prime(n):
        return n, 1
    for f in range(2, r+1):
        p = iroot(n, f)
        if p**f == n and rational_prime(p):
            return p, f
    return None


def ptrim(a, p):
    return trim([x % p for x in a])


def prem(a, b, p):
    a = ptrim(a, p); b = ptrim(b, p)
    assert b
    iv = pow(b[-1], -1, p)
    while len(a) >= len(b):
        k = len(a)-len(b); v = a[-1]*iv % p
        for j, x in enumerate(b):
            a[k+j] = (a[k+j]-v*x) % p
        a = ptrim(a, p)
    return a


def pgcd(a, b, p):
    a = ptrim(a, p); b = ptrim(b, p)
    while b:
        a, b = b, prem(a, b, p)
    iv = pow(a[-1], -1, p)
    return tuple(x*iv % p for x in a)


def pmulmod(a, b, f, p):
    if not a or not b:
        return []
    c = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] = (c[i+j]+x*y) % p
    return prem(c, f, p)


def ppowmod(a, n, f, p):
    out = [1]
    while n:
        if n & 1:
            out = pmulmod(out, a, f, p)
        n //= 2
        if n:
            a = pmulmod(a, a, f, p)
    return out


def irreducible(f, p):
    d = len(f)-1
    if d < 1 or f[-1] != 1:
        return False
    if d == 1:
        return True
    x = prem([0, 1], f, p); xp = x
    needed = {d//q for q in factors(d)}
    for i in range(1, d+1):
        xp = ppowmod(xp, p, f, p)
        diff = [0]*max(len(xp), len(x))
        for j in range(len(xp)):
            diff[j] += xp[j]
        for j in range(len(x)):
            diff[j] -= x[j]
        if i in needed and len(pgcd(f, diff, p)) > 1:
            return False
    return not ptrim(diff, p)


@lru_cache(None)
def pi_bounds(bits):
    def atan_inv(q):
        total = Q(0); j = 0
        while True:
            term = Q(1, (2*j+1)*q**(2*j+1))
            total += term if j % 2 == 0 else -term
            nxt = Q(1, (2*j+3)*q**(2*j+3))
            if nxt < Q(1, 2**(bits+8)):
                return (total-nxt, total) if j % 2 == 0 else (total, total+nxt)
            j += 1
    a, b = atan_inv(5); c, d = atan_inv(239)
    return 16*a-4*d, 16*b-4*c


def trig_bounds(num, den, bits, cosine):
    """Dyadic enclosure of sin/cos(2*pi*num/den), Taylor plus Lipschitz error."""
    num %= den
    if 2*num > den:
        num -= den
    plo, phi_ = pi_bounds(bits+16)
    lo, hi = 2*Q(num, den)*plo, 2*Q(num, den)*phi_
    if lo > hi:
        lo, hi = hi, lo
    x = (lo+hi)/2; uncertainty = (hi-lo)/2
    term = Q(1) if cosine else x; total = term; j = 0
    while True:
        k = 2*j if cosine else 2*j+1
        nxt = -term*x*x/((k+1)*(k+2))
        j += 1
        if abs(nxt) < Q(1, 2**(bits+8)) and k >= 6:
            error = abs(nxt)+uncertainty
            scale = 1 << bits
            low = (total-error)*scale; high = (total+error)*scale
            return low.numerator//low.denominator, -((-high.numerator)//high.denominator)
        total += nxt; term = nxt


class EnergyField:
    def __init__(self, m):
        assert m >= 3 and m % 4 != 2, 'use reduced conductor'
        self.m = m; self.polynomial = phi_poly(m); self.r = len(self.polynomial)-1
        self.s = self.r//2; self.w = m if m % 2 == 0 else 2*m
        self.zero = (0,)*self.r; self.one = (1,)+(0,)*(self.r-1)
        self.zeta = self.times_x(self.one)
        self.powers = [self.one]
        for _ in range(1, m):
            self.powers.append(self.times_x(self.powers[-1]))
        self.conj_columns = [self.powers[-j % m] for j in range(self.r)]
        self.rho = self.zeta if m % 2 == 0 else tuple(-x for x in self.powers[(m+1)//2])
        self.rho_inverse = self.conjugate(self.rho)
        self.rotations = [self.mul(self.rho, self.powers[j]) for j in range(self.r)]
        self.inverse_rotations = [self.mul(self.rho_inverse, self.powers[j]) for j in range(self.r)]
        self.gram = [[ramanujan(m, i-j) for j in range(self.r)] for i in range(self.r)]
        self.norm_cache = {}; self.prime_cache = {}; self.trig_cache = {}
        self.discriminant = m**self.r
        for p in factors(m):
            self.discriminant //= p**(self.r//(p-1))
        root = isqrt(self.discriminant)
        if root*root < self.discriminant:
            root += 1
        bound = Q(4, 3)**self.s * Q(factorial(self.r), self.r**self.r) * root
        self.minkowski_floor = bound.numerator//bound.denominator
        self.ldl = self.make_ldl()

    def times_x(self, a):
        last = a[-1]
        return tuple((a[i-1] if i else 0)-last*self.polynomial[i] for i in range(self.r))

    def mul(self, a, b):
        out = [0]*self.r; column = a
        for value in b:
            if value:
                for j in range(self.r):
                    out[j] += value*column[j]
            column = self.times_x(column)
        return tuple(out)

    def conjugate(self, a):
        return tuple(sum(a[j]*self.conj_columns[j][i] for j in range(self.r)) for i in range(self.r))

    def energy(self, a):
        v = sum(a[i]*a[j]*self.gram[i][j] for i in range(self.r) for j in range(self.r))
        assert v % 2 == 0
        return v//2

    def norm(self, a):
        a = tuple(a)
        if a not in self.norm_cache:
            cols = [a]
            for _ in range(1, self.r):
                cols.append(self.times_x(cols[-1]))
            value = det([[cols[j][i] for j in range(self.r)] for i in range(self.r)])
            assert value >= 0
            self.norm_cache[a] = value
        return self.norm_cache[a]

    def sign_part(self, a, imaginary=False):
        conjugate = self.conjugate(a)
        zero = all(a[i] == conjugate[i] if imaginary else a[i] == -conjugate[i] for i in range(self.r))
        if zero:
            return 0
        bits = 48
        while True:
            key = bits, imaginary
            if key not in self.trig_cache:
                self.trig_cache[key] = [trig_bounds(j, self.m, bits, not imaginary) for j in range(self.r)]
            low = high = 0
            for x, (lo, hi) in zip(a, self.trig_cache[key]):
                low += x*(lo if x >= 0 else hi)
                high += x*(hi if x >= 0 else lo)
            if low > 0:
                return 1
            if high < 0:
                return -1
            bits *= 2

    def in_sector(self, a):
        if not any(a):
            return False
        tie = False
        for columns in (self.rotations, self.inverse_rotations):
            rotated = tuple(sum(a[j]*columns[j][i] for j in range(self.r)) for i in range(self.r))
            sign = self.sign_part(tuple(a[i]-rotated[i] for i in range(self.r)))
            if sign < 0:
                return False
            tie = tie or sign == 0
        return not tie or self.sign_part(a, True) < 0

    def prime_record(self, a):
        a = tuple(a)
        if a in self.prime_cache:
            return self.prime_cache[a]
        n = self.norm(a); pf = prime_power(n, self.r) if n >= 2 else None
        answer = None
        if pf:
            p, f = pf
            g = pgcd(self.polynomial, a, p)
            if len(g)-1 == f and irreducible(g, p):
                answer = {'norm': n, 'p': p, 'residue_degree': f, 'factor': list(g)}
        self.prime_cache[a] = answer
        return answer

    def make_ldl(self):
        n = self.r; lower = [[Q(int(i == j)) for j in range(n)] for i in range(n)]; d = []
        for j in range(n):
            dj = Q(self.gram[j][j])-sum(lower[j][k]**2*d[k] for k in range(j))
            assert dj > 0; d.append(dj)
            for i in range(j+1, n):
                lower[i][j] = (Q(self.gram[i][j])-sum(lower[i][k]*lower[j][k]*d[k] for k in range(j)))/dj
        return lower, d

    def ellipsoid(self, energy_bound):
        """Every integral point of E<=bound, exact rational square-root bounds."""
        lower, diagonal = self.ldl; values = [0]*self.r
        def visit(j, budget):
            if j < 0:
                yield tuple(values); return
            center = -sum(lower[i][j]*values[i] for i in range(j+1, self.r))
            radius2 = budget/diagonal[j]
            p, q = center.numerator, center.denominator
            v = radius2*q*q
            root = isqrt(v.numerator//v.denominator)
            lo = -((-(p-root))//q); hi = (p+root)//q
            for x in range(lo, hi+1):
                remainder = budget-diagonal[j]*(x-center)**2
                assert remainder >= 0
                values[j] = x
                yield from visit(j-1, remainder)
        yield from visit(self.r-1, Q(2*energy_bound))

    def expected_ideals(self, cutoff, omit_ramified=True):
        total = 0
        for p in range(2, cutoff+1):
            if not rational_prime(p):
                continue
            if omit_ramified and self.m % p == 0:
                continue
            q = self.m; power = 1
            while q % p == 0:
                q //= p; power *= p
            e = phi(power); f = 1
            if q != 1:
                residue = p % q
                while residue != 1:
                    residue = residue*p % q; f += 1
            if p**f <= cutoff:
                total += self.r//(e*f)
        return total

    def enumerate_minima(self, energy_bound):
        minima = {}; scanned = 0; sector = 0
        for a in self.ellipsoid(energy_bound):
            scanned += 1
            if not self.in_sector(a):
                continue
            sector += 1
            record = self.prime_record(a)
            if not record:
                continue
            key = record['p'], tuple(record['factor'])
            value = self.energy(a), a
            if key not in minima or value < minima[key]:
                minima[key] = value
        return {key: value[1] for key, value in minima.items()}, {'ellipsoid_vectors': scanned, 'sector_vectors': sector}

    def pool(self, count, energy_bound=None, progress=None):
        if self.m not in (7, 9, 15, 16):
            raise NotImplementedError('the finite-example pool driver is restricted to the four certified class-number-one fields; GN1 gives the separate all-field enumeration algorithm')
        bound = energy_bound or 3*self.s
        while True:
            minima, stats = self.enumerate_minima(bound)
            small = sorted((a for a in minima.values() if self.norm(a) <= self.minkowski_floor),key=lambda a:(self.norm(a), a))
            class_ok = len(small) == self.expected_ideals(self.minkowski_floor, False)
            candidates = sorted((a for (p, _), a in minima.items() if self.m % p), key=lambda a:(self.norm(a), a))
            cutoff = self.norm(candidates[count-1]) if len(candidates) >= count else None
            through = [a for a in candidates if self.norm(a) <= cutoff] if cutoff else []
            complete = class_ok and cutoff is not None and len(through) == self.expected_ideals(cutoff)
            if progress:
                progress({'m':self.m,'energy_bound':bound,'classes_found':len(minima),'class_number_one_certified':class_ok,'norm_cutoff':cutoff,'complete':complete,**stats})
            if complete:
                cert = {'energy_bound':bound,'norm_cutoff':cutoff,'all_through_cutoff':[list(a) for a in through],
                    'class_number_certificate':{'method':'minkowski-all-small-primes','discriminant':self.discriminant,'bound_floor':self.minkowski_floor,'prime_generators':[list(a) for a in small]}}
                return candidates[:count], cert
            if energy_bound is not None:
                raise ValueError('fixed energy bound does not certify this entire prefix')
            bound += max(1, self.s)


def lines(n, dimension):
    """Full fixed/increasing/decreasing-coordinate lines, deduplicated cell sets."""
    found = set()
    choices = list(range(n))+['+', '-']
    for spec in itertools.product(choices, repeat=dimension):
        if not any(x in ('+', '-') for x in spec):
            continue
        cells = []
        for t in range(n):
            index = 0
            for x in spec:
                coordinate = t if x == '+' else n-1-t if x == '-' else x
                index = index*n+coordinate
            cells.append(index)
        found.add(tuple(sorted(cells)))
    return sorted(found)


def certificate(field, n, dimension, pool, completeness, arrangement, metadata):
    required = lines(n, dimension); records = []
    for cells in required:
        total = tuple(sum(arrangement[i][j] for i in cells) for j in range(field.r))
        prime = field.prime_record(total)
        assert prime, (cells, total)
        records.append({'cells':list(cells),'sum':list(total),**prime})
    return {'format':'cyclotomic-energy-array-v1','conductor':field.m,'dimension':dimension,'side':n,
        'polynomial':list(field.polynomial),'normalization':'trace-energy-sector-lex-v1',
        'omitted_rational_primes':sorted(factors(field.m)),'pool':[list(a) for a in pool],
        'pool_completeness':completeness,'arrangement':[list(a) for a in arrangement],
        'lines':records,'metadata':metadata}
