"""Literal finite replay of the order-five obstruction and universal isotope construction."""
from itertools import permutations
P=[[0,1,2,3,4],[1,0,3,4,2],[2,3,4,0,1],[3,4,1,2,0],[4,2,0,1,3]]
def latin(T):
    R=set(range(len(T)))
    return all(set(x)==R for x in T+list(zip(*T)))
def accepts(T):
    if not latin(T):return False
    c=T[0][0]
    return all(T[x][x]==c and T[c][T[c][x]]==x and T[T[x][c]][c]==x for x in range(len(T)))
def parastrophe(T,s):
    m=len(T);U=[[None]*m for _ in range(m)]
    for i in range(m):
        for j in range(m):
            w=i,j,T[i][j]
            U[w[s[0]]][w[s[1]]]=w[s[2]]
    return U
def factor(D,e):
    n=len(D); I=list(range(n));J=list(range(n));seen=set()
    for j in range(n):
        if j in seen:continue
        C=[j];x=D[j]
        while x!=j:C.append(x);x=D[x]
        seen.update(C)
        for i,a in enumerate(C):I[a]=C[-i%len(C)];J[a]=C[(-i-1)%len(C)]
    assert I[e]==J[e]==e and all(I[J[x]]==D[x] for x in range(n))
    return I,J
assert latin(P) and P[0]==list(range(5)) and [x[0] for x in P]==list(range(5))
for T in (P,[[(i+j)%3 for j in range(3)] for i in range(3)]):
    n=len(T)
    for s in permutations(range(3)):
        Q=parastrophe(T,s)
        for d in range(n):
            U=[[Q[i][Q[j].index(d)] for j in range(n)] for i in range(n)]
            for e in range(n):
                A=U[e];B=[U[x][e] for x in range(n)]
                D=[A.index(y) for y in B];I,J=factor(D,e)
                W=[[I[A.index(z)] for z in row] for row in U]
                assert accepts(W)
for s in permutations(range(3)):
    assert not (accepts(parastrophe(P,s)) and accepts(parastrophe([[(i+j)%3 for j in range(3)] for i in range(3)],s)))
print('All six parastrophes excluded by literal loop controls; output relabeling verified for every anchor.')
