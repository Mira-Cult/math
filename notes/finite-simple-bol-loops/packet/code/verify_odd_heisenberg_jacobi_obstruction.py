#!/usr/bin/env python3
"""Exact q=2311 Jacobi obstruction, using only integer arithmetic.

Run with Python 3.11+ and assertions enabled.  This certificate checks the
finite arithmetic; the singularity implication is proved in the manuscript.
"""
assert __debug__

from math import isqrt
q = 2311
assert all(q % k for k in range(2, isqrt(q) + 1))
assert q % 12 == 7
assert all(pow(3, k, 7) != 1 for k in range(1, 6))
assert pow(3, 6, 7) == 1
assert all(pow(3, (q-1)//p, q) != 1 for p in (2,3,5,7,11))
assert pow(3, q-1, q) == 1
log = {}
x = 1
for k in range(q-1):
    assert x not in log
    log[x] = k
    x = 3*x % q
assert x == 1 and len(log) == q-1
counts = [0]*7
for x in range(1,q):
    y = (1-x) % q
    if y:
        sign = 1 if pow(y,(q-1)//2,q)==1 else -1
        counts[(4*log[x]) % 7] += sign
assert counts == [17,-12,-12,-20,18,22,-14]
a = [1,2,2,0,2,0]
c = [0]*11
for i,u in enumerate(a):
    for j,v in enumerate(a):
        c[i+j] += u*v
for k in range(10,5,-1):
    t = c[k] % 3
    for j in range(6):
        c[k-6+j] -= t
assert [t % 3 for t in c[:6]] == [2,0,0,0,0,0]
assert [v % 3 for v in counts[:6]] == [(a[i]+counts[6]) % 3 for i in range(6)]
print('q=2311: primitive root and Jacobi-square obstruction verified')
