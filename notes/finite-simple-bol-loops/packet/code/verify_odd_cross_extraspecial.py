#!/usr/bin/env python3
"""Finite deterministic controls for the cross-extraspecial coordinate loop.

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

def vadd(u,v,add): return tuple(add(x,y) for x,y in zip(u,v))
def vneg(u,neg): return tuple(neg(x) for x in u)
def vmul(c,u,mul): return tuple(mul(c,x) for x in u)
def j(u,neg): return (u[1],neg(u[0]))
def dot(u,v,add,mul): return add(mul(u[0],v[0]),mul(u[1],v[1]))
fadd=lambda a,b:(a+b)%13
fneg=lambda a:(-a)%13
fmul=lambda a,b:a*b%13
zero=(0,0)

def loop(x,y):
    u,a,v,b=x; U,A,V,B=y
    omegap=dot(u,j(U,en),ea,em)
    omegaq=dot(v,j(V,fneg),fadd,fmul)
    return (vadd(u,vmul(ep(zeta,b),U,em),ea),
            (a+A+trace(omegap))%3,
            vadd(v,vmul(pow(3,a,13),V,fmul),fadd),
            (b+B+omegaq)%13)

# A group element is (x_p,y_p,z_p,x_q,y_q,z_q,i,j).
# Multiply actual Heisenberg elements after applying the left torus action;
# coset normalization below uses right multiplication by generators of H.
def hg(x,y,z,X,Y,Z,add,neg,mul,central,mod):
    pair=add(dot(x,Y,add,mul),neg(dot(y,X,add,mul)))
    return vadd(x,X,add),vadd(y,Y,add),(z+Z+pow(2,-1,mod)*central(pair))%mod

def gm(g,h):
    x,y,z,v,w,t,i,jj=g; X,Y,Z,V,W,T,I,J=h
    X=vmul(ep(zeta,jj),X,em); Y=vmul(ep(zeta,-jj),Y,em)
    V=vmul(pow(3,i,13),V,fmul); W=vmul(pow(3,-i,13),W,fmul)
    xp,yp,zp=hg(x,y,z,X,Y,Z,ea,en,em,trace,3)
    xq,yq,zq=hg(v,w,t,V,W,T,fadd,fneg,fmul,lambda q:q,13)
    return xp,yp,zp,xq,yq,zq,(i+I)%3,(jj+J)%13

def section(q):
    u,a,v,b=q
    return (vneg(vmul(ep(zeta,-b),j(u,en),em),en),u,0,
            vneg(vmul(pow(3,-a,13),j(v,fneg),fmul),fneg),v,0,(-a)%3,(-b)%13)

def normalize(g):
    # Cancel torus with (a_p z_p)^I (a_q z_q)^J in H, then remove
    # both first-coordinate translations by a further right S_p x S_q element.
    i,jj=g[6:]; I=(-i)%3; J=(-jj)%13
    h=(zero,zero,I,zero,zero,J,I,J)
    v=gm(g,h)
    h=(vneg(v[0],en),zero,0,vneg(v[3],fneg),zero,0,0,0)
    v=gm(v,h)
    assert v[0]==zero and v[3]==zero and v[6:]==(0,0)
    return v[1],v[2],v[4],v[5]

one=(zero,0,zero,0)
x=(zero,1,zero,0); y=(zero,0,(1,0),0); z=(zero,0,(0,1),0)
lhs=loop(loop(x,y),loop(z,x)); rhs=loop(loop(x,loop(y,z)),x)
assert lhs==(zero,2,(3,3),3) and rhs==(zero,2,(3,3),1)
rng=random.Random(20261115)
def sample(): return ((rng.randrange(27),rng.randrange(27)),rng.randrange(3),(rng.randrange(13),rng.randrange(13)),rng.randrange(13))
samples=[one,x,y,z]+[sample() for _ in range(100)]
for q in samples:
    assert normalize(section(q))==q
    assert loop(one,q)==q and loop(q,one)==q
    u,a,v,b=q
    inv=(vneg(vmul(ep(zeta,-b),u,em),en),(-a)%3,
         vneg(vmul(pow(3,-a,13),v,fmul),fneg),(-b)%13)
    assert loop(q,inv)==one and loop(inv,q)==one
for _ in range(500):
    a,b,c=(rng.choice(samples) for _ in range(3))
    assert normalize(gm(section(a),section(b)))==loop(a,b)
    # left Bol: x (y (x z)) = (x (y x)) z.
    assert loop(a,loop(b,loop(a,c)))==loop(loop(a,loop(b,a)),c)
print('F27 modulus t^3-t+1; zeta encoding:',zeta,'; eta: 3')
print('Moufang witness (xy)(zx):',lhs,'; (x(yz))x:',rhs)
print('104 section/identity/inverse controls; 500 group-coset and left-Bol sample controls passed')
print('Finite samples only: no universal identity, simplicity, or exhaustive table claimed.')
