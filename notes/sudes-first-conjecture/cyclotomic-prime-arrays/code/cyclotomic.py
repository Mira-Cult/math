#!/usr/bin/env python3
"""Exact producer arithmetic. No floating embedding decides membership.

Prime elements are certified by O/(alpha), not by prime rational norm alone.
The independently authored checker must not import this module.
"""
from functools import lru_cache
from itertools import product, combinations
from math import isqrt

ZERO = (0, 0, 0, 0)
ONE = (1, 0, 0, 0)


def add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x-y for x, y in zip(a, b))


def neg(a):
    return tuple(-x for x in a)


def scale(c, a):
    return tuple(c*x for x in a)


def sign_surd(a, b, d):
    """Sign of a+b sqrt(d), for integral a,b and nonsquare d>0."""
    if not b:
        return (a > 0) - (a < 0)
    if not a:
        return (b > 0) - (b < 0)
    if (a > 0) == (b > 0):
        return (a > 0) - (a < 0)
    cmp = (a*a > d*b*b) - (a*a < d*b*b)
    return cmp if a > 0 else -cmp


def trim(f):
    f = list(f)
    while f and not f[-1]:
        f.pop()
    return f


def rem(f, g, p):
    f, g = trim([x % p for x in f]), trim([x % p for x in g])
    if not g:
        raise ZeroDivisionError
    inv = pow(g[-1], -1, p)
    while len(f) >= len(g):
        q, k = f[-1]*inv % p, len(f)-len(g)
        for j, c in enumerate(g):
            f[k+j] = (f[k+j]-q*c) % p
        f = trim(f)
    return f


def gcd_poly(f, g, p):
    f, g = trim(f), trim(g)
    while g:
        f, g = g, rem(f, g, p)
    if not f:
        return []
    inv = pow(f[-1], -1, p)
    return [x*inv % p for x in f]


def power_poly(a, n, g, p):
    def pmul(x, y):
        z = [0]*(len(x)+len(y)-1)
        for i, u in enumerate(x):
            for j, v in enumerate(y):
                z[i+j] += u*v
        return rem(z, g, p)
    r = [1]
    while n:
        if n & 1:
            r = pmul(r, a)
        a = pmul(a, a)
        n >>= 1
    return r


def irreducible(g, p):
    """Rabin criterion, degree at most four."""
    d = len(g)-1
    if d < 1:
        return False
    x = rem([0, 1], g, p)
    h = x
    for j in range(1, d+1):
        h = power_poly(h, p, g, p)
        delta = [(h[k] if k < len(h) else 0) -
                 (x[k] if k < len(x) else 0)
                 for k in range(max(len(h), len(x)))]
        if j <= d//2 and len(gcd_poly(g, delta, p)) > 1:
            return False
    return not trim([v % p for v in delta])


def prime_power(n):
    """Exact trial division. Return (p,e) iff n is a prime power >1."""
    if n < 2:
        return None
    p = 2
    while p*p <= n and n % p:
        p = 3 if p == 2 else p+2
    if p*p > n:
        return n, 1
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return (p, e) if n == 1 else None


def primes_to(n):
    sieve = bytearray(b'\1')*(n+1)
    if n >= 0:
        sieve[0] = 0
    if n >= 1:
        sieve[1] = 0
    for p in range(2, isqrt(n)+1):
        if sieve[p]:
            sieve[p*p:n+1:p] = b'\0'*((n-p*p)//p+1)
    return [i for i in range(2, n+1) if sieve[i]]


class Field:
    def __init__(self, m):
        self.m = m
        self.phi = {5:(1,1,1,1,1), 8:(1,0,0,0,1),
                    12:(1,0,-1,0,1)}[m]
        self.w = {5:10, 8:8, 12:12}[m]
        self.a2 = {5:2, 8:3, 12:5}[m]
        self.z = (0,1,0,0)
        self.powers = [ONE]
        for _ in range(1, m):
            self.powers.append(self.mul(self.powers[-1], self.z))
        self.rho = neg(self.powers[3]) if m == 5 else self.z
        self.u = {5:(0,0,-1,-1), 8:(1,1,0,-1), 12:(1,1,0,0)}[m]
        self.lambda2 = self.mul(self.u, self.conjugate(self.u))
        self.gamma = sub(self.z, self.conjugate(self.z))
        if m == 5:
            self.low = self.mul(self.rho, sub(ONE, self.z))
        elif m == 8:
            self.low = self.mul(self.z, sub(ONE, self.z))
        else:
            self.low = self.conjugate(self.u)
        self.high = self.conjugate(self.low)

    def mul(self, a, b):
        c = [0]*7
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                c[i+j] += x*y
        for k in (6,5,4):
            v = c[k]
            if v:
                for j in range(4):
                    c[k-4+j] -= v*self.phi[j]
        return tuple(c[:4])

    def automorphism(self, a, k):
        return tuple(sum(a[j]*self.powers[j*k % self.m][i]
                         for j in range(4)) for i in range(4))

    def conjugate(self, a):
        return self.automorphism(a, self.m-1)

    def real_sign(self, a):
        if self.m == 5:
            b, c = -a[2], a[0]-a[2]
            assert a == (c-b,0,-b,-b)
            return sign_surd(2*c-b,b,5)
        if self.m == 8:
            assert a[2] == 0 and a[3] == -a[1]
            return sign_surd(a[0],a[1],2)
        assert a[2] == 0 and a[1] == -2*a[3]
        return sign_surd(a[0],-a[3],3)

    def imaginary_sign(self, a):
        return self.real_sign(neg(self.mul(sub(a,self.conjugate(a)),self.gamma)))

    def canonical(self, a):
        if a == ZERO:
            return False
        # Half-open angular sector, decided in the real quadratic field.
        if self.imaginary_sign(self.mul(a,self.high)) < 0:
            return False
        if self.imaginary_sign(self.mul(a,self.low)) >= 0:
            return False
        aa = self.mul(a,self.conjugate(a))
        bb = self.automorphism(aa,self.a2)
        return (self.real_sign(sub(self.mul(aa,self.lambda2),bb)) >= 0 and
                self.real_sign(sub(aa,self.mul(bb,self.lambda2))) < 0)

    @lru_cache(maxsize=500000)
    def norm(self, a):
        aa = self.mul(a,self.conjugate(a))
        n = self.mul(aa,self.automorphism(aa,self.a2))
        assert n[1:] == (0,0,0) and n[0] >= 0
        return n[0]

    @lru_cache(maxsize=500000)
    def prime_certificate(self, a):
        n = self.norm(a)
        pe = prime_power(n)
        if pe is None:
            return None
        p, e = pe
        if e > 4:
            return None
        g = gcd_poly(self.phi, [x % p for x in a], p)
        if len(g)-1 != e or not irreducible(g,p):
            return None
        return {'norm':n, 'rational_prime':p, 'residue_degree':e,
                'quotient_polynomial':g}

    def expected_ideal_count(self, B):
        count = 0
        for p in primes_to(B):
            if self.m % p == 0:
                continue
            f, x = 1, p % self.m
            while x != 1:
                x = x*p % self.m
                f += 1
                assert f <= 4
            if p**f <= B:
                count += 4//f
        return count

    def pool(self, count):
        """Complete norm prefix, including cut ties and all residue degrees.

        A scan terminates only when its certified distinct prime ideals account
        for ALL unramified ideals through the proposed norm cutoff. Class number
        one and exact normalization make this a completeness certificate.
        """
        H = 1
        while True:
            values = []
            for a in product(range(-H,H+1),repeat=4):
                if not self.canonical(a):
                    continue
                c = self.prime_certificate(a)
                if c is not None and self.m % c['rational_prime']:
                    values.append(a)
            values.sort(key=lambda a:(self.norm(a),a))
            if len(values) >= count:
                B = self.norm(values[count-1])
                covered = [a for a in values if self.norm(a) <= B]
                expected = self.expected_ideal_count(B)
                if len(covered) == expected:
                    return values[:count], {'coefficient_scan_radius':H,
                        'norm_cutoff':B,'complete_tie_count':expected,
                        'all_through_cutoff':[list(a) for a in covered]}
            H += 1


def lines(n, D):
    result = set()
    for k in range(1,D+1):
        for active in combinations(range(D),k):
            fixed = [j for j in range(D) if j not in active]
            for signs in product((1,-1),repeat=k-1):
                directions = dict(zip(active,(1,)+signs))
                for f in product(range(n),repeat=len(fixed)):
                    const = dict(zip(fixed,f))
                    cells = []
                    for t in range(n):
                        x = tuple(const[j] if j in const else
                                  (t if directions[j] == 1 else n-1-t)
                                  for j in range(D))
                        idx = 0
                        for y in x:
                            idx = n*idx+y
                        cells.append(idx)
                    result.add(tuple(sorted(cells)))
    return sorted(result)


def certificate(field, n, D, arrangement, metadata=None):
    pool, completeness = field.pool(n**D)
    records = []
    for line in lines(n,D):
        total = tuple(sum(arrangement[i][j] for i in line) for j in range(4))
        prime = field.prime_certificate(total)
        if prime is None:
            raise ValueError(('composite line',line,total,field.norm(total)))
        records.append({'cells':list(line),'sum':list(total),'prime':prime})
    if sorted(arrangement) != sorted(pool):
        raise ValueError('wrong prescribed pool')
    return {'format':'cyclotomic-prime-array-v1','conductor':field.m,
            'dimension':D,'side':n,'polynomial':list(field.phi),
            'normalization':'balanced-log-symmetric-sector-v1',
            'omitted_rational_primes':[p for p in primes_to(field.m) if field.m%p==0],
            'pool':[list(a) for a in pool], 'pool_completeness':completeness,
            'arrangement':[list(a) for a in arrangement], 'lines':records,
            'metadata':metadata or {}}


if __name__ == '__main__':
    import argparse,json
    parser = argparse.ArgumentParser()
    parser.add_argument('--m',type=int,choices=(5,8,12),required=True)
    parser.add_argument('--count',type=int,default=27)
    args = parser.parse_args()
    f = Field(args.m)
    p,c = f.pool(args.count)
    print(json.dumps({'m':args.m,'pool':p,'norms':[f.norm(a) for a in p],
                      'completeness':c},indent=2))
