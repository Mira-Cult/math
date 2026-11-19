#!/usr/bin/env python3
"""Exact checks for beyond_forest_bridge.md; no external dependencies."""
from fractions import Fraction


def fwht(a):
    a = list(a)
    h = 1
    while h < len(a):
        for i in range(0, len(a), 2*h):
            for j in range(i, i+h):
                u, v = a[j], a[j+h]
                a[j], a[j+h] = u+v, u-v
        h *= 2
    return a


def anf_degree(a):
    a = list(a)
    n = (len(a)-1).bit_length()
    for i in range(n):
        for s in range(1 << n):
            if s & (1 << i):
                a[s] ^= a[s ^ (1 << i)]
    return max((s.bit_count() for s, v in enumerate(a) if v), default=-1)


def v2(a):
    a = abs(a)
    return (a & -a).bit_length()-1


def check_layers():
    count = noncharacters = 0
    for n in range(5):
        N = 1 << n
        for truth in range(1 << N):
            f = [1-2*((truth >> x) & 1) for x in range(N)]
            W = fwht(f)
            m = min(v2(w) for w in W if w)
            P = [int(w != 0 and v2(w) == m) for w in W]
            delta = anf_degree(P)
            if m < n:
                assert delta <= m-1, (n, truth, W, m, delta)
                noncharacters += 1
            else:
                assert sum(bool(w) for w in W) == 1
            count += 1
    return count, noncharacters


def check_majority():
    W = fwht([1 if sum(1-2*((x >> i)&1) for i in range(3)) > 0
              else -1 for x in range(8)])
    p = [Fraction(w*w, 64) for w in W]
    D = {s for s in range(8) if p[s]}
    assert D == {1, 2, 4, 7}
    assert all(p[s] == Fraction(1, 4) for s in D)
    assert sum(p[s]*s.bit_count() for s in range(8)) == Fraction(3, 2)
    for i in range(3):
        assert sum(p[s] for s in range(8) if s >> i & 1) == Fraction(1, 2)
        for j in range(i):
            for a in range(2):
                for b in range(2):
                    assert sum(p[s] for s in range(8)
                               if (s >> i)&1 == a and (s >> j)&1 == b) == Fraction(1, 4)
    sublaws = []
    for truth in range(256):
        V = fwht([1-2*((truth >> x)&1) for x in range(8)])
        supp = {s for s, v in enumerate(V) if v}
        if supp <= D:
            assert len(supp) in (1, 4)
            if len(supp) == 4:
                assert all(abs(V[s]) == 4 for s in D)
            sublaws.append(supp)
    assert len(sublaws) == 16
    assert sum(len(s) == 1 for s in sublaws) == 8
    assert sum(len(s) == 4 for s in sublaws) == 8
    # q_T is uniform: each positive p/q ratio is2, so KL is exactly1bit.
    assert sum(p[s] for s in D) == 1
    assert all(p[s] / Fraction(1, 8) == 2 for s in D)
    return len(sublaws)


def check_completion():
    vals = [3,1,1,0,2,0,1,0,3,1,1,0,3,1,2,1]
    assert sum(4**v for v in vals) == 4**4
    delta = anf_degree([int(v == 0) for v in vals])
    assert delta == 3
    eps = 4+delta-4
    assert 2*(1+eps) == 8


if __name__ == '__main__':
    count, noncharacters = check_layers()
    sublaws = check_majority()
    check_completion()
    print(f'PASS: {count} Boolean functions; {noncharacters} strengthened layers; '
          f'{sublaws} majority-supported Boolean functions; exact tree projection '
          'and eight-bit independent fair completion bound.')
