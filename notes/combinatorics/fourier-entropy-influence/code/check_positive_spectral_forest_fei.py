#!/usr/bin/env python3
"""Exact checks for positive_spectral_forest_fei.md.

The finite checks do not prove the universal theorem. The manuscript gives
its induction. All mathematical assertions checked here use integers and
Fractions; no entropy is evaluated with floating-point logarithms.
"""
from collections import Counter
from fractions import Fraction
from itertools import product


def algebraic_degree(values, n):
    coeff=list(values)
    for i in range(n):
        for s in range(1 << n):
            if s >> i & 1:
                coeff[s] ^= coeff[s ^ (1 << i)]
    return max((s.bit_count() for s,a in enumerate(coeff) if a), default=-1)


def walsh(values):
    a=list(values)
    width=1
    while width < len(a):
        for start in range(0,len(a),2*width):
            for j in range(start,start+width):
                x,y=a[j],a[j+width]
                a[j],a[j+width]=x+y,x-y
        width *= 2
    return a


def v2(n):
    n=abs(n)
    assert n
    return (n & -n).bit_length()-1


def labelled_trees(n):
    if n==2:
        yield [(0,1)]
        return
    for word in product(range(n),repeat=n-2):
        degree=[1]*n
        for v in word:
            degree[v] += 1
        edges=[]
        for v in word:
            u=next(i for i,d in enumerate(degree) if d==1)
            edges.append((u,v))
            degree[u] -= 1
            degree[v] -= 1
        a,b=[i for i,d in enumerate(degree) if d==1]
        edges.append((a,b))
        yield edges


def minimum_layer_check():
    checked=0
    for n in range(5):
        for truth in product((-1,1),repeat=1 << n):
            W=walsh(truth)
            m=min(v2(a) for a in W if a)
            P=[int(a != 0 and v2(a)==m) for a in W]
            assert algebraic_degree(P,n) <= m
            checked += 1
    print('PASS: minimum Walsh layer degree on all Boolean tables n<=4:',checked)


def energy(n, edges, fields, couplings):
    return [sum(fields[i]*(s >> i & 1) for i in range(n))+
            sum(J*(s >> i & 1)*(s >> j & 1)
                for (i,j),J in zip(edges,couplings))
            for s in range(1 << n)]


def check_one_energy(n, edges, fields, couplings):
    a=energy(n,edges,fields,couplings)
    lo,hi=min(a),max(a)
    delta=algebraic_degree([int(v==lo) for v in a],n)
    kappa=n-delta
    assert delta+hi-lo >= n
    v=[x-lo for x in a]
    weights=[4**x for x in v]
    Z=sum(weights)
    # Complement any coordinate with marginal greater than 1/2. This
    # minimizes B over all coordinate labelings, while preserving kappa.
    marg=[sum(weights[s] for s in range(1 << n) if s >> i & 1)
          for i in range(n)]
    B_num=sum(x*w for x,w in zip(v,weights))+2*sum(min(m,Z-m) for m in marg)
    assert B_num >= (kappa+1)*Z
    for root in range(n):
        branches=[[a[s] for s in range(1 << n) if s >> root & 1 == b]
                  for b in (0,1)]
        R=max(max(z)-min(z) for z in branches)
        assert kappa <= R
        branch_kappa=[n-1-algebraic_degree([int(x==min(z)) for x in z],n-1)
                      for z in branches]
        cross_rhs=max(branch_kappa)
        shift=min(branches[0])-min(branches[1])
        if shift:
            # Every other root field is either a unique-minimum branch or
            # the unique tying field. These exhaust the possible kappa values.
            tied=[a[t]+shift*(t >> root & 1) for t in range(1 << n)]
            tied_kappa=n-algebraic_degree([int(x==min(tied)) for x in tied],n)
            cross_rhs=max(cross_rhs,tied_kappa)
        assert B_num >= cross_rhs*Z
        if kappa == hi-lo == R:
            # The strengthening proves the only possible field is the one
            # at which the conditional ground energies coincide.
            assert min(branches[0]) == min(branches[1])
    return a,delta


def range_degree_check():
    checked=0
    for n in range(2,5):
        for edges in labelled_trees(n):
            for fields in product(range(-1,2),repeat=n):
                for couplings in product((-1,1),repeat=n-1):
                    check_one_energy(n,edges,fields,couplings)
                    checked += 1
    for n in (5,6):
        edges=[(i,i+1) for i in range(n-1)]
        for fields in product(range(-1,2),repeat=n):
            for couplings in product((-1,1),repeat=n-1):
                check_one_energy(n,edges,fields,couplings)
                checked += 1
    print('PASS: range/degree, positive Gibbs slack, all root-field cross cases:',checked)


def examples():
    # Known positive four-path component.
    a=[3,1,1,0,2,0,1,0,3,1,1,0,3,1,2,1]
    assert sum(4**x for x in a)==4**4
    assert algebraic_degree([int(x==0) for x in a],4)==3
    assert 2*(4+3-4)==6
    # Known positive six-path component.
    h=(1,-1,-2,-1,-3,-2)
    J=(1,1,1,1,2)
    a=[x+5 for x in energy(6,[(i,i+1) for i in range(5)],h,J)]
    assert min(a)==0 and max(a)==6 and sum(4**x for x in a)==4**7
    assert algebraic_degree([int(x==0) for x in a],6)==4
    assert 2*(7+4-6)==10
    # Actual Boolean star counterexample to the forbidden-state strengthening.
    for k in range(3,6):
        N=2*k
        n=N+2
        truth=[]
        for x in range(1 << n):
            u=1-2*(x & 1)
            v=1-2*(x >> 1 & 1)
            y=x >> 2
            bent=(-1)**sum((y >> (2*j) & 1)*(y >> (2*j+1) & 1)
                          for j in range(k))
            truth.append(bent if v==1 else u)
        W=walsh(truth)
        assert sum(a*a for a in W)==4**n
        minimum=min(v2(a) for a in W if a)
        vals=[None if not a else v2(a)-minimum for a in W]
        ground=[int(v==0) for v in vals]
        assert algebraic_degree(ground,n)==1
        norm=sum(4**v for v in vals if v is not None)
        assert norm==4**(k+1)
        Ev=sum(Fraction(4**v*v,norm) for v in vals if v is not None)
        influence=sum(Fraction(4**v*s.bit_count(),norm)
                      for s,v in enumerate(vals) if v is not None)
        assert Ev==Fraction(k,2)
        assert influence==Fraction(k,2)+1
        assert Ev+2*influence==Fraction(3*k,2)+2 < n-1
        entropy=2*(k+1)-2*Ev
        assert entropy==k+2==2*influence
    print('PASS: exact core defects and Boolean hard-zero star counterexamples.')


def main():
    minimum_layer_check()
    range_degree_check()
    examples()
    print('All exact checks passed. Universal proofs are in the manuscript; finite checks are diagnostics.')


if __name__=='__main__':
    main()
