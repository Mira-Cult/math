#!/usr/bin/env python3
"""Finite controls for the uniform Bol and Moufang proofs."""
from itertools import product

def bol(d, support):
    n = 2 << d
    m = n // 2
    return [[(((a // m) ^ (b // m) ^ (int(a % m in support) * (b & 1))) * m)
              + ((a % m) ^ (b % m)) for b in range(n)] for a in range(n)]

def latin(t):
    n = len(t)
    u = set(range(n))
    assert all(set(r) == u for r in t)
    assert all(set(r) == u for r in zip(*t))

def commutant(t):
    return sum(all(t[x][y] == t[y][x] for y in range(len(t)))
               for x in range(len(t)))

def distance(t,u):
    return sum(a != b for r,s in zip(t,u) for a,b in zip(r,s))

for d in (3,4,5):
    A,B=bol(d,{2}),bol(d,{2,4})
    n=len(A)
    for t in (A,B):
        latin(t)
        assert all(t[0][x] == t[x][0] == x and t[x][x] == 0 for x in range(n))
        assert all(t[x][t[y][t[x][z]]] == t[t[x][t[y][x]]][z]
                   for x,y,z in product(range(n),repeat=3))
        assert any(t[t[x][y]][z] != t[x][t[y][z]]
                   for x,y,z in product(range(n),repeat=3))
    assert distance(A,B) == n
    assert (commutant(A),commutant(B)) == (n//2-2,n//2-4)
    print(f"Bol order {n}: distance {n}, different commutants")

# Relabel a cyclic group by one transposition swapping its identity.
n=256
f=list(range(n))
f[0],f[1]=f[1],f[0]
A=[[(a+b)%n for b in range(n)] for a in range(n)]
B=[[f[(f[a]+f[b])%n] for b in range(n)] for a in range(n)]
assert all(f[A[a][b]] == B[f[a]][f[b]] for a,b in product(range(n),repeat=2))
assert A[0][1]==1 and B[1][0]==0 and B[1][1]==1
d=distance(A,B)
assert 0 < 20*d < n*n
print(f"Moufang order {n}: distance {d}, isomorphic with different identity labels")
