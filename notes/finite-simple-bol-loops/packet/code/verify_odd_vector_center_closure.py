#!/usr/bin/env python3
"""Exact finite central-subspace closure control; does not enumerate loops."""
from itertools import product

def subspaces(p):
    allv=set(product(range(p),repeat=2)); zero=frozenset({(0,0)})
    lines={frozenset((k*x%p,k*y%p) for k in range(p)) for x,y in allv if (x,y)!=(0,0)}
    return [zero]+sorted(lines,key=lambda s:sorted(s))+[frozenset(allv)]
def span_add(s, vectors,p):
    out=set(s)
    for x,y in vectors:
        out={((a+k*x)%p,(b+k*y)%p) for a,b in out for k in range(p)}
    return frozenset(out)
def step(c,d):
    # a1 -> b1 -> a2 -> b2 -> a1 (source coordinate activates target axis).
    paxes=[]; qaxes=[]
    if any(a for a,b in c): qaxes.append((1,0))
    if any(b for a,b in c): qaxes.append((0,1))
    if any(a for a,b in d): paxes.append((0,1))
    if any(b for a,b in d): paxes.append((1,0))
    return span_add(c,paxes,3),span_add(d,qaxes,13)

ss=subspaces(3); tt=subspaces(13)
assert len(ss)==6 and len(tt)==16
fixed=[]; longest=0
for start in product(ss,tt):
    current=start; n=0
    while True:
        nxt=step(*current)
        if nxt==current: break
        current=nxt;n+=1
    longest=max(longest,n)
    if current==start:fixed.append(start)
    if start!=(ss[0],tt[0]): assert current==(ss[-1],tt[-1])
assert set(fixed)=={(ss[0],tt[0]),(ss[-1],tt[-1])}
print('F3² subspaces:',len(ss),'F13² subspaces:',len(tt),'tuples:',len(ss)*len(tt))
print('Fixed tuples: zero and full; every nonzero seed closes to full; maximum iterations:',longest)
print('Finite center-closure check only; no folder, loop, or simplicity theorem verified.')
