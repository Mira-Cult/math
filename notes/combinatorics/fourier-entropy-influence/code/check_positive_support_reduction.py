#!/usr/bin/env python3
"""Exact tests of Boolean full-support completion; no universal FEI search.

Default: all truth tables on n<=3, every physical point, k=1,2;
and all n=4 truth tables, x0=0, k=1. Exact claims use integer arithmetic.
The final asymptotic table is a floating-point illustration, explicitly not a
certificate for limits. No external dependencies.
"""

from fractions import Fraction
from math import exp, log2, log1p


def walsh(values):
    out = list(values)
    step = 1
    while step < len(out):
        for base in range(0, len(out), 2 * step):
            for j in range(step):
                a, b = out[base+j], out[base+j+step]
                out[base+j], out[base+j+step] = a+b, a-b
        step *= 2
    return out


def influence_numerator(values, n):
    # Counts oriented sensitive edges; I = result / 2^n.
    return sum(values[x] != values[x ^ (1 << i)]
               for x in range(1 << n) for i in range(n))


def check_one(f, n, x0, k):
    m, size = 1 << n, 1 << (n+k)
    # Old input coordinates are low bits; z0=0 without loss for these tests.
    g = [f[x % m] for x in range(size)]
    g[x0] *= -1
    wf, wg = walsh(f), walsh(g)
    assert all(w % 4 == 2 for w in wg)
    assert sum(w*w for w in wg) == size*size
    for mask, w in enumerate(wg):
        old = (1 << k) * wf[mask] if mask < m else 0
        character = -1 if (mask & x0).bit_count() % 2 else 1
        assert w == old - 2*f[x0]*character
    sf = sum(f[x0] != f[x0 ^ (1 << i)] for i in range(n))
    ig = influence_numerator(g, n+k)
    inf = influence_numerator(f, n)
    assert ig - (1 << k)*inf == 2*(n+k-2*sf)
    assert sum(mask.bit_count()*w*w for mask, w in enumerate(wg)) == size*ig
    old_squares = [(1 << (2*k))*w*w for w in wf] + [0]*(size-m)
    delta_num = sum(abs(w*w-p) for w, p in zip(wg, old_squares))
    # TV=delta_num/(2 size^2), epsilon=2/size, L1=sum|W_f|/m.
    assert delta_num*m <= 4*size*(m+sum(abs(w) for w in wf))
    assert sum(w*w for w in wg[m:]) == 4*(size-m)
    assert sum(w*w for w in wg[:m]) == size*size-4*(size-m)


def check_full_interaction():
    cases = ((2, 2), (2, 4), (3, 2), (3, 4))
    for n, m in cases:
        big_n = n*m
        size = 1 << big_n
        block_mask = (1 << n)-1
        f = [(-1)**sum(((x >> (j*n)) & block_mask) == 0
                       for j in range(m)) for x in range(size)]
        assert f[0] == 1
        g = list(f)
        g[0] = -1
        wg = walsh(g)
        b = (1 << (n-1))-1
        for mask, w in enumerate(wg):
            ell = sum(bool((mask >> (j*n)) & block_mask) for j in range(m))
            assert w == (1 << m)*(-1)**ell*b**(m-ell)-2
            assert w % 4 == 2
        assert (influence_numerator(g, big_n)
                == m*n*(1 << (big_n+1-n))-2*big_n)
        # All pairs have a nonzero conditional odds ratio at remaining bits0.
        for i in range(big_n):
            for j in range(i):
                p00 = wg[0]**2
                p10 = wg[1 << i]**2
                p01 = wg[1 << j]**2
                p11 = wg[(1 << i) | (1 << j)]**2
                assert p00*p11 != p10*p01
        # Delta log p = log(product_positive/product_negative).
        # Equal numbers of parity signs cancel the normalization denominator.
        prod_positive = 1
        prod_negative = 1
        for mask, w in enumerate(wg):
            if (big_n-mask.bit_count()) % 2 == 0:
                prod_positive *= w*w
            else:
                prod_negative *= w*w
        assert prod_positive < prod_negative
    print(f"PASS: {len(cases)} exact full-interaction spectra; max N=12")


def main():
    count = 0
    for n in range(1, 5):
        m = 1 << n
        points = range(m) if n <= 3 else (0,)
        extra = (1, 2) if n <= 3 else (1,)
        for truth in range(1 << m):
            f = [-1 if (truth >> x) & 1 else 1 for x in range(m)]
            for x0 in points:
                for k in extra:
                    check_one(f, n, x0, k)
                    count += 1
    print(f"PASS: {count} exact full-support completions")
    check_full_interaction()
    print("DIAGNOSTIC ONLY: tensorized rare-point sequence")
    print("n  N  I  L/N  D/N  mean_upper  max_atom_upper  H/I")
    for n in (3, 4, 6, 8, 12, 20, 30):
        eps = 2.0**(1-n)
        p0 = (1-eps)**2
        q = eps*(2-eps)
        log_mean = log1p(-eps)
        h = -2*p0*log_mean/log1p(1) + q*(2*n-2)
        l = p0*(n+log_mean/log1p(1))+q
        m = n*(1 << (n-1))
        big_n = n*m
        assert Fraction(n*n, big_n) == Fraction(1, 1 << (n-1))
        print(n, big_n, n*n, f"{l/n:.10f}", f"{1-h/n:.10f}",
              f"{exp(-n):.4g}", f"{exp(-2*n):.4g}", f"{h/(n*eps):.10f}")


if __name__ == "__main__":
    main()
