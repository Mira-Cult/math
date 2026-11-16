#!/usr/bin/env python3
"""Finite deterministic controls for the extraspecial operator coordinate loop.

No enumeration or proof of the folder, Bol identity, or simplicity is claimed.
All arithmetic uses integers and Python's standard library.
"""
import random

# F_27 encoded as c0+3*c1+9*c2; t^3=t-1.
def ea(a,b):
    return sum((((a//3**i)%3+(b//3**i)%3)%3)*3**i for i in range(3))
def en(a):
    return sum(((-(a//3**i)%3)%3)*3**i for i in range(3))
def em(a,b):
    aa=[a//3**i%3 for i in range(3)]; bb=[b//3**i%3 for i in range(3)]
    c=[0]*5
    for i in range(3):
        for j in range(3): c[i+j]+=aa[i]*bb[j]
    for k in (4,3):
        c[k-2]+=c[k]; c[k-3]-=c[k]
    return sum((c[i]%3)*3**i for i in range(3))
def ep(a,n):
    if n<0: return ep(ep(a,25),-n)
    v=1
    while n:
        if n&1: v=em(v,a)
        a=em(a,a); n//=2
    return v
def trace(a):
    v=ea(ea(a,ep(a,3)),ep(a,9)); assert v in (0,1,2); return v
zeta=next(x for x in range(2,27) if ep(x,13)==1 and x!=1)
assert all(ep(zeta,i)!=1 for i in range(1,13))
assert pow(3,3,13)==1 and 3!=1
# Four-dimensional self-adjoint N=(T,T^t), N^2=0.
def add(u,v,p): return tuple(ea(x,y) if p==3 else (x+y)%13 for x,y in zip(u,v))
def neg(u,p): return tuple(en(x) if p==3 else -x%13 for x in u)
def action(u,a,b,p):
    if p==13: return tuple(pow(3,a%3,13)*x%13 for x in u)
    n=(u[1],0,0,u[2]); c=a%3
    w=tuple(ea(x,em(c,y)) for x,y in zip(u,n))
    return tuple(em(ep(zeta,b%13),x) for x in w)
def beta(u,v,p):
    if p==13: return (u[0]*v[1]-u[1]*v[0])%13
    z=0
    for i in range(2): z=ea(z,ea(em(u[i],v[i+2]),en(em(u[i+2],v[i]))))
    return trace(z)
z3=(0,)*4; z13=(0,)*2

def loop(x,y):
    u,a,v,b=x; U,A,V,B=y
    return add(u,action(U,a,b,3),3),(a+A-beta(u,U,3))%3,add(v,action(V,a,b,13),13),(b+B-beta(v,V,13))%13

def heis(x,y,z,X,Y,Z,p):
    return add(x,X,p),add(y,Y,p),(z+Z+pow(2,-1,p)*(beta(x,Y,p)+beta(y,X,p)))%p

def gm(g,h):
    x,y,z,v,w,t,a,b=g; X,Y,Z,V,W,T,A,B=h
    X=action(X,a,b,3);Y=action(Y,-a,-b,3)
    V=action(V,a,b,13);W=action(W,-a,-b,13)
    X,Y,Z=heis(x,y,z,X,Y,Z,3);V,W,T=heis(v,w,t,V,W,T,13)
    return X,Y,Z,V,W,T,(a+A)%3,(b+B)%13

def sec(q):
    u,a,v,b=q
    return neg(action(u,-a,-b,3),3),u,0,neg(action(v,-a,-b,13),13),v,0,-a%3,-b%13

def normal(g):
    a,b=g[-2:]; A=-a%3;B=-b%13
    g=gm(g,(z3,z3,A,z13,z13,B,A,B))
    g=gm(g,(neg(g[0],3),z3,0,neg(g[3],13),z13,0,0,0))
    assert g[0]==z3 and g[3]==z13 and g[-2:]==(0,0)
    return g[1],g[2],g[4],g[5]

one=(z3,0,z13,0); x=(z3,1,z13,0);y=(z3,0,(1,0),0);z=(z3,0,(0,1),0)
lhs=loop(loop(x,y),loop(z,x));rhs=loop(loop(x,loop(y,z)),x)
assert lhs==(z3,2,(3,3),10) and rhs==(z3,2,(3,3),12)
assert action((0,1,0,0),1,0,3)==(1,1,0,0)
rng=random.Random(20261115)
def sample():return (tuple(rng.randrange(27) for _ in range(4)),rng.randrange(3),tuple(rng.randrange(13) for _ in range(2)),rng.randrange(13))
samples=[one,x,y,z]+[sample() for _ in range(100)]
for a in samples:
    assert normal(sec(a))==a and loop(a,one)==a and loop(one,a)==a
for _ in range(500):
    a,b,c=(rng.choice(samples) for _ in range(3))
    assert normal(gm(sec(a),sec(b)))==loop(a,b)
    assert loop(a,loop(b,loop(a,c)))==loop(loop(a,loop(b,a)),c)
print('F27 root encoding',zeta,'; own-prime N is nonzero, N²=0')
print('Moufang LHS',lhs,'RHS',rhs)
print('104 section/identity and 500 group-coset/left-Bol sample checks passed')
print('Finite controls only; no proof of simplicity, classification or universal identities.')
