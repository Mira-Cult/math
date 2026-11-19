#!/usr/bin/env python3
"""Exact 16-state check; the nonrealizability proof is in the manuscript."""
values = []
for mask in range(16):
    a, b, c, d = [(mask >> i) & 1 for i in range(4)]
    v = b + c - a*b - b*c - c*d + a*d
    x1, x2, x3, x4 = [1-2*s for s in (a,b,c,d)]
    assert 2*(1-2*v) == x1*x2+x2*x3+x3*x4-x1*x4
    values.append(v)
assert values == [0,0,1,0,1,1,1,0,0,1,1,1,0,1,0,0]
assert values.count(0) == values.count(1) == 8
ground = [int(v == 0) for v in values]
for i in range(4):
    for mask in range(16):
        if mask & (1 << i):
            ground[mask] ^= ground[mask ^ (1 << i)]
assert [s for s, c in enumerate(ground) if c] == [0,2,3,4,6,9,12]
degree = max(s.bit_count() for s, c in enumerate(ground) if c)
kappa = 4-degree
assert degree == kappa == 2
assert sum(4**v for v in values) == 40 < 2*5**kappa
print('PASS: exact four-cycle obstruction; Boolean exclusion is analytic')
