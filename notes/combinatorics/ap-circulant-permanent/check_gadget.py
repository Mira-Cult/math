"""Independent exhaustive verification of the clique-width reduction.

This does not call or reuse the four-counter permanent recurrence.
"""
from functools import lru_cache
from itertools import permutations
from math import prod
from random import Random


def gadget(u, v, t):
    n = len(u)
    a = [[0] * (10*n) for _ in range(10*n)]
    def edge(i, j, w):
        a[i][j] = a[j][i] = w
    for i in range(n):
        # row ports U,V,T are positions 0,2,4
        # column ports V,U,T are positions 5,7,9
        for q, w in enumerate((1, u[i], t, 1)):
            edge(10*i+q, 10*i+q+1, w)
        for q, w in enumerate((1, v[i], 1, 1)):
            edge(10*i+5+q, 10*i+6+q, w)
        for j in range(n):
            edge(10*i, 10*j+7, 1)
            edge(10*i+2, 10*j+5, 1)
            if j < i:
                edge(10*i+4, 10*j+9, 1)
    return a


def matching_sum(a):
    n = len(a)
    neighbors = [sum(1 << j for j, x in enumerate(r) if x) for r in a]
    @lru_cache(None)
    def rec(mask):
        if not mask:
            return 1
        indices = [i for i in range(n) if mask >> i & 1]
        i = min(indices, key=lambda k: (neighbors[k] & mask).bit_count())
        return sum(a[i][j]*rec(mask ^ (1 << i) ^ (1 << j))
                   for j in indices if a[i][j])
    return rec((1 << n)-1)


def permanent(u, v, t):
    return sum(prod(u[i]+v[j]+t*(j<i) for i, j in enumerate(p))
               for p in permutations(range(len(u))))


def expression(u, v, t):
    """Evaluate a weighted linear clique expression with 11 labels."""
    labels, edges = {}, {}
    # Active labels RU,RV,CU,CV,CT; dead D; temporaries Q0..Q4.
    def new(vertex, label):
        labels[vertex] = label
    def join(left, right, weight):
        for x in [x for x in labels if labels[x] == left]:
            for y in [y for y in labels if labels[y] == right]:
                key = tuple(sorted((x,y)))
                if key not in edges:
                    edges[key] = weight
    def rename(old, new):
        for x in labels:
            if labels[x] == old:
                labels[x] = new
    def path(offset, weights):
        for q in range(5):
            new(offset+q, f'Q{q}')
        for q, w in enumerate(weights):
            join(f'Q{q}', f'Q{q+1}', w)
    for i in range(len(u)):
        path(10*i, (1,u[i],t,1))
        for q, c in ((0,'CU'),(2,'CV'),(4,'CT')):
            join(f'Q{q}', c, 1)
        for q, c in enumerate(('RU','D','RV','D','D')):
            rename(f'Q{q}', c)
        path(10*i+5, (1,v[i],1,1))
        join('Q0','RV',1)
        join('Q2','RU',1)
        for q, c in enumerate(('CV','D','CU','D','CT')):
            rename(f'Q{q}', c)
    a = [[0]*len(labels) for _ in labels]
    for (i,j), w in edges.items():
        a[i][j] = a[j][i] = w
    return a


def main():
    r = Random(37082026)
    cases = 0
    for n in range(6):
        for _ in range(15):
            u = [r.randrange(-3,4) for _ in range(n)]
            v = [r.randrange(-3,4) for _ in range(n)]
            t = r.randrange(-3,4)
            a = gadget(u,v,t)
            assert expression(u,v,t) == a, (u,v,t,'expression')
            actual = matching_sum(a)
            wanted = permanent(u,v,t)
            assert actual == wanted, (u,v,t,actual,wanted)
            cases += 1
    print(f'{cases} exhaustive matching/permutation checks and clique-expression graph checks passed.')


if __name__ == '__main__':
    main()
