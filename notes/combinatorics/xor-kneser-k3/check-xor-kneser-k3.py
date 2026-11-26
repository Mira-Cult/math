"""Independent replay of the exceptional ten-complement-pair construction."""
from itertools import combinations
U = frozenset(range(6))
pairs = [(A, U-A) for x in combinations(U, 3) if 0 in (A:=frozenset(x))]
assert len(pairs) == 10
for n in range(81, 103):
    q = n//3
    s = min(q,30)
    p = [2 + (j < s-20) for j in range(10)]
    assert sum(p) == s
    C = []
    first = 0
    for (A,B), k in zip(pairs,p):
        edges = [(i,j) for i in range(k) for j in range(k)]
        if k==2:
            edges += [(i,i) for i in range(k)]
        assert len(edges)==3*k
        C.extend((A, frozenset(first+a for a,(u,v) in enumerate(edges) if i==u)) for i in range(k))
        C.extend((B, frozenset(first+a for a,(u,v) in enumerate(edges) if i==v)) for i in range(k))
        first += len(edges)
    assert first <= n and len(C)==2*s==len(set(C))
    assert all(len(A)==len(B)==3 for A,B in C)
    for (A,B),(D,E) in combinations(C,2):
        assert (A.isdisjoint(D)) != (B.isdisjoint(E))
    assert (len(C) > q+27) == (84<=n<=98)
print("PASS: exact declared complement-block cliques and excess at orders 84–98.")
