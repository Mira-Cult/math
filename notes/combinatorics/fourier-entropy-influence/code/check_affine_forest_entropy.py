#!/usr/bin/env python3
"""Exact finite checks for the affine-forest entropy theorem.

No enumeration is used as proof. Dependencies: Python 3.11+ standard library.
Default: all coefficient choices in the stated ranges on the unlabeled
connected trees through four vertices; every root and seven root fields.
Also checks a concrete high-arity coefficient and the strict constant bound.
"""
from itertools import product
from math import log2
from random import Random

def ground_degree(values,n):
    lo=min(values)
    a=[int(v==lo) for v in values]
    for i in range(n):
        for s in range(1<<n):
            if s&(1<<i):a[s]^=a[s^(1<<i)]
    return max(s.bit_count() for s,c in enumerate(a) if c)

def data(n,edges,fields,couplings):
    vals=[sum(fields[i]*((s>>i)&1) for i in range(n))+
          sum(j*((s>>u)&1)*((s>>v)&1) for (u,v),j in zip(edges,couplings))
          for s in range(1<<n)]
    lo=min(vals)
    z=sum(1<<(2*(v-lo)) for v in vals)
    return z,n-ground_degree(vals,n)

def finite_trees():
    trees={1:[()],2:[((0,1),)],3:[((0,1),(1,2))],
           4:[((0,1),(1,2),(2,3)),((0,1),(0,2),(0,3))]}
    own=cross=0
    for n,shapes in trees.items():
        for edges in shapes:
            for root in range(n):
                rest=[i for i in range(n) if i!=root]
                for fields_rest in product(range(-2,3),repeat=n-1):
                    h=[0]*n
                    for i,x in zip(rest,fields_rest):h[i]=x
                    for couplings in product((-2,-1,1,2),repeat=n-1):
                        ds=[]
                        for field in range(-3,4):
                            h[root]=field
                            z,k=data(n,edges,h,couplings)
                            ds.append((z,k))
                            if n>1 or field:
                                assert z>=2*5**k,(n,edges,h,couplings,z,k)
                                own+=1
                        for a,(za,ka) in enumerate(ds):
                            for b,(zb,kb) in enumerate(ds):
                                if a!=b:
                                    assert zb>=5**ka,(n,edges,h,couplings,a,b,ds)
                                    if n>1: assert za*zb>=5**(ka+kb+1),(n,edges,h,couplings,a,b,ds)
                                    cross+=1
        print(f'n={n}: cumulative own={own}, cross={cross}')
    return own,cross

def random_trees():
    rng=Random(20261117)
    own=cross=0
    for n in range(5,11):
        for _ in range(100):
            edges=[(i,rng.randrange(i)) for i in range(1,n)]
            h=[rng.randrange(-4,5) for _ in range(n)]
            couplings=[rng.choice((-4,-3,-2,-1,1,2,3,4)) for _ in edges]
            root=rng.randrange(n)
            ds=[]
            for a in range(-3,4):
                h[root]=a
                z,k=data(n,edges,h,couplings);ds.append((z,k))
                assert z>=2*5**k;own+=1
            for a,(za,ka) in enumerate(ds):
                for b,(zb,kb) in enumerate(ds):
                    if a!=b:
                        assert zb>=5**ka
                        assert za*zb>=5**(ka+kb+1)
                        cross+=1
    return own,cross

def high_arity():
    for m in (1,2,3):
        r=4*m
        vals=[]
        for s in range(1<<r):
            t=[(s>>i)&1 for i in range(r)]
            def v(a,b,c,d):return 3-2*a-2*b-c+a*b+b*c+c*d
            e=v(s.bit_count()%2,t[1],t[2],t[3])
            e+=sum(v(*t[4*j:4*j+4]) for j in range(1,m))
            vals.append(e)
        # Ordinary real multilinear/Mobius coefficient, not F2 ANF.
        top=sum((-1)**(r-s.bit_count())*v for s,v in enumerate(vals))
        assert top==(-1)**r*3*2**(r-2),(m,top)
    assert 5**25>2**58
    print('top-degree coefficients and C_aff<17 checked exactly')

if __name__=='__main__':
    print('exhaustive',finite_trees())
    print('seeded random',random_trees())
    high_arity()
    print('C_aff=',4+4/log2(5/4),'(display only)')
