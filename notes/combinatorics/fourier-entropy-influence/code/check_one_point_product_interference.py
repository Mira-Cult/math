#!/usr/bin/env python3
"""Exact finite identities behind the one-point product FEI theorem.

All assertions use integers or fractions. The theorem's entropy inequality is
proved analytically in the manuscript; the displayed ratios are diagnostics.
"""

from fractions import Fraction
from math import log2


def walsh(values):
    out = list(values)
    step = 1
    while step < len(out):
        for base in range(0, len(out), 2*step):
            for j in range(step):
                x, y = out[base+j], out[base+j+step]
                out[base+j], out[base+j+step] = x+y, x-y
        step *= 2
    return out


def edge_count(values, n):
    return sum(values[x] != values[x ^ (1 << i)]
               for x in range(1 << n) for i in range(n))


def check(blocks):
    n = sum(blocks)
    size = 1 << n
    masks = []
    pos = 0
    for block in blocks:
        masks.append(((1 << block)-1) << pos)
        pos += block
    f = [(-1)**sum((x & mask) == 0 for mask in masks) for x in range(size)]
    g = list(f)
    g[0] *= -1
    wf, wg = walsh(f), walsh(g)
    assert all(v % 4 == 2 for v in wg)
    assert all(v != 0 for v in wf)
    assert all(y == x-2*(-1)**len(blocks) for x, y in zip(wf, wg))
    inf = edge_count(f, n)
    ing = edge_count(g, n)
    assert ing == inf-2*n
    assert sum(s.bit_count()*v*v for s, v in enumerate(wg)) == size*ing
    eps = [Fraction(1, 1 << (b-1)) for b in blocks]
    delta = Fraction(2, size)
    assert Fraction(inf, size) == sum(b*e for b, e in zip(blocks, eps))
    assert sum(b*e*e for b, e in zip(blocks, eps)) >= n*delta
    for mask, e in zip(masks, eps):
        old = sum(v*v for s, v in enumerate(wf) if s & mask)
        new = sum(v*v for s, v in enumerate(wg) if s & mask)
        assert Fraction(new-old, size*size) == -delta*(2-e)
    chi_numerator = sum(Fraction((y*y-x*x)**2, x*x) for x, y in zip(wf, wg))
    assert chi_numerator <= 25*size
    # Exact nonzero full mixed logarithmic difference via integer products.
    upper = lower = 1
    for s, value in enumerate(wg):
        if (n-s.bit_count()) % 2 == 0:
            upper *= value*value
        else:
            lower *= value*value
    sign = -(-1)**(n+len(blocks))
    assert (upper > lower) if sign == 1 else (upper < lower)
    # All pairs really depend conditionally: find a nonzero conditional minor.
    for i in range(n):
        for j in range(i):
            mask = (1 << i) | (1 << j)
            found = False
            for s in range(size):
                if s & mask:
                    continue
                values = [wg[s]**2, wg[s | (1 << i)]**2,
                          wg[s | (1 << j)]**2, wg[s | mask]**2]
                if values[0]*values[3] != values[1]*values[2]:
                    found = True
                    break
            assert found
    entropy = -sum((v*v/(size*size))*log2(v*v/(size*size)) for v in wg)
    print(f"PASS exact identities: {blocks}; N={n}; numerical H/I={entropy/(ing/size):.12f}")


def main():
    assert 3**9 > 2**14  # Only finite nontrivial logarithmic seed comparison.
    cases = ((2, 2), (2, 3), (3, 3), (2, 2, 2), (2, 2, 3),
             (2, 3, 4), (2, 2, 2, 2), (3, 4, 5))
    for blocks in cases:
        check(blocks)
    print(f"PASS: {len(cases)} exact spectra; unequal blocks and both parities; max N=12")


if __name__ == '__main__':
    main()
