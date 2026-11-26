from itertools import combinations_with_replacement
from math import comb

M=16
S=frozenset(x for x in range(M) if x%4!=0 or x==8)

def sums(xs):
    a=set()
    for x in xs:
        a|={x}|{(x+y)%M for y in a}
    return a

assert len(S)==13 and 0 not in S
count=0
for gens in combinations_with_replacement(sorted(S),5):
    assert not sums(gens)<=S, gens
    count+=1
assert count==comb(17,5)==6188
A={i for i in range(80) if i%M in S}
assert len(A)==65>64 and 80%5==0
print(f'PASS: all {count} base multisets excluded; preimage size {len(A)} > 64.')
