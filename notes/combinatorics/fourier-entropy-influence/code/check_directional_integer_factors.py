#!/usr/bin/env python3
"""Exact finite audits for directional_integer_factors.md.

Default: core identities for odd ell<=9; actual Boolean Walsh transforms
for ell=1,3 (dimensions 12 and 16); one-decrease cylinder factors on <=8
bits; 100 seeded integral-power factor tensors on <=7 bits. Universal
inequalities are proved in the manuscript, not established by these tests.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from math import comb
from random import Random


def energy(label: int, ell: int) -> int:
    a, b, c = (label >> i & 1 for i in range(3))
    d = label >> 3
    phi = int(d.bit_count() > ell // 2)
    return 3 - 2*a - 2*b - c + a*b + b*c + c*phi


def fwht(values: list[int]) -> None:
    width = 1
    while width < len(values):
        for base in range(0, len(values), 2*width):
            for j in range(base, base+width):
                a, b = values[j], values[j+width]
                values[j], values[j+width] = a+b, a-b
        width *= 2


def core_audit(ell: int) -> None:
    m, k = ell+3, (ell+7)//2
    es = [energy(s, ell) for s in range(1 << m)]
    ws = [4**v for v in es]
    total = sum(ws)
    assert total == 4**k
    ev = Fraction(sum(w*v for w,v in zip(ws,es)), total)
    assert ev == Fraction(167,64)
    j_core = Fraction(sum(w*s.bit_count() for s,w in enumerate(ws)), total)
    alpha = Fraction(ell*comb(ell-1,(ell-1)//2), 1 << ell)
    expected_i = ell+Fraction(1061,256)+Fraction(33,128)*alpha
    assert j_core+k == expected_i
    expected_h = 2*ell+Fraction(281,32)
    assert 4*k-2*ev == expected_h
    assert expected_h <= 4*expected_i
    # Nonzero full-degree majority coefficient in the real multilinear basis.
    coefficient = sum((-1)**(ell-d.bit_count())
                      for d in range(1 << ell) if d.bit_count() > ell//2)
    assert coefficient == (-1)**((ell-1)//2)*comb(ell-1,(ell-1)//2)
    # Actual factorization (16), with all adverse factors unary.
    for s,v in enumerate(es):
        a,b,c = (s >> i & 1 for i in range(3))
        phi = int((s >> 3).bit_count() > ell//2)
        assert m+v == m-2+2*(1-a)+2*(1-b)+(1-c)+a*b+b*c+c*phi
    print(f"core ell={ell}: norm=4^{k}, H={expected_h}, I={expected_i}, clique>={ell+1}")


def boolean_audit(ell: int) -> None:
    m, k = ell+3, (ell+7)//2
    n = m+2*k
    es = [energy(s,ell) for s in range(1 << m)]
    labels = [-1] * (1 << (2*k))
    depths = [k-v for v in es]
    cursor = 0
    # Canonical quaternary prefix code, represented by contiguous blocks.
    for s in sorted(range(1 << m), key=lambda z:(depths[z],z)):
        block = 4**(k-depths[s])
        assert cursor % block == 0
        for y in range(cursor,cursor+block):
            assert labels[y] == -1
            labels[y] = s
        cursor += block
    assert cursor == len(labels) and min(labels) >= 0
    vals = [0] * (1 << n)
    for y,s in enumerate(labels):
        free_pairs = k-depths[s]
        bent_parity = sum(((y >> (2*j)) & 1)*((y >> (2*j+1)) & 1)
                          for j in range(free_pairs)) & 1
        for x in range(1 << m):
            vals[(y << m)|x] = 1-2*(bent_parity ^ ((x&s).bit_count() & 1))
    assert set(vals) == {-1,1}
    fwht(vals)
    assert all(abs(w) == 1 << (m+es[z & ((1 << m)-1)])
               for z,w in enumerate(vals))
    norm = 1 << (2*n)
    assert sum(w*w for w in vals) == norm
    hi = sum(w*w*(2*n-2*(abs(w).bit_length()-1)) for w in vals)
    ii = sum(w*w*z.bit_count() for z,w in enumerate(vals))
    h, inf = Fraction(hi,norm), Fraction(ii,norm)
    alpha = Fraction(ell*comb(ell-1,(ell-1)//2),1 << ell)
    assert h == 2*ell+Fraction(281,32)
    assert inf == ell+Fraction(1061,256)+Fraction(33,128)*alpha
    assert h <= 4*inf
    print(f"Boolean ell={ell}: exact {1<<n}-entry Walsh transform PASS; H={h}, I={inf}")


def cylinder_audit() -> None:
    count = 0
    for n in range(1,9):
        # Every mask/assignment through n=5; representatives for n=6..8.
        masks = range(1 << n) if n <= 5 else [0,1,(1 << n)-1,(1 << n)-2]
        for mask in masks:
            assignments = [s for s in range(1 << n) if s & ~mask == 0]
            for target in assignments:
                vals = [1 if s&mask == target else 7 for s in range(1 << n)]
                for s,a in enumerate(vals):
                    b = sum(not(s >> i & 1) and a > vals[s | (1 << i)]
                            for i in range(n))
                    assert b <= 1
                count += 1
    print(f"complement-cylinder factors: {count} exact factors PASS")


def random_factor_audit() -> None:
    rng = Random(20261117)
    for _ in range(100):
        n = rng.randrange(1,8)
        fs: list[list[int]] = []
        for _ in range(rng.randrange(1,8)):
            mask = rng.randrange(1 << n)
            target = rng.randrange(1 << n) & mask
            scale = rng.randrange(1,4)
            # All values are exponents of two; zero means factor value one.
            fs.append([0 if s&mask == target else scale for s in range(1 << n)])
        c = rng.randrange(4)
        e = [c+sum(f[s] for f in fs) for s in range(1 << n)]
        load = [sum(f[s]*sum(not(s >> i & 1) and f[s]>f[s | (1 << i)]
                            for i in range(n)) for f in fs) for s in range(1 << n)]
        assert all(b<=v for b,v in zip(load,e))
        # (6), (7), and the raw conclusion after common normalization.
        for i in range(n):
            for s in range(1 << n):
                if s >> i & 1:
                    continue
                t = s | (1 << i)
                logu = sum(f[s] for f in fs if f[s]>f[t])
                assert 4**e[s]-4**e[t] <= 4**e[s]*logu
        z = sum(4**v for v in e)
        lnum = sum(4**v*v for v in e)
        jnum = sum(4**v*s.bit_count() for s,v in enumerate(e))
        assert n*z-lnum <= 2*jnum
    print("100 seeded positive integer-factor tensors: exact edge/global inequalities PASS")


def rare_point_core_audit() -> None:
    for n in range(2,13):
        vals = [1] * (1 << n)
        vals[0] = -1
        fwht(vals)
        assert vals[0] == (1 << n)-2
        assert set(vals[1:]) == {-2}
        # Reduce the exceptional Fourier coefficient; leave all signs intact.
        vals[0] = 2
        assert all(abs(w) == 2 for w in vals)
        wh = Fraction(sum(w*w for w in vals), 1 << (2*n))
        inf = Fraction(sum(w*w*s.bit_count() for s,w in enumerate(vals)), 1 << (2*n))
        hraw = 2*(n-1)*wh
        assert hraw == 4*inf-2*wh  # exact scalar credit, log_2 c=1
        # Multiplication by an arbitrary character translates the atom.
        for target in [0,1,(1 << n)-1]:
            shifted = [vals[s^target] for s in range(1 << n)]
            assert all(abs(w) == 2 for w in shifted)
    print("rare-point and character-shift cores n=2..12: exact Walsh/scalar credit PASS")
    for m in range(3,12):
        cap = (1 << (m-1))-1
        # (m-1)log_2 M>2, using exact integers and no logarithm rounding.
        assert cap**(m-1) > 4
        for i in range(2*m):
            singleton_amplitude = 4*cap
            other_block_neighbors = [4]*m
            assert singleton_amplitude**m > singleton_amplitude*4**m
            assert len(other_block_neighbors) == m
    print("two-block singleton obstruction m=3..11: exact multiplicative certificates PASS")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--boolean-ell", type=int, nargs="*", default=[1,3])
    args = parser.parse_args()
    for ell in range(1,10,2):
        core_audit(ell)
    for ell in args.boolean_ell:
        assert ell >= 1 and ell % 2 == 1
        boolean_audit(ell)
    cylinder_audit()
    random_factor_audit()
    rare_point_core_audit()
    # Sharpness for integer-valued raw entropy: a physical point indicator.
    for n in range(1,20):
        hraw = Fraction(2*n,1 << n)
        inf = Fraction(n,1 << (n+1))
        assert hraw == 4*inf
    print("integer point-indicator sharpness: exact PASS")


if __name__ == "__main__":
    main()
