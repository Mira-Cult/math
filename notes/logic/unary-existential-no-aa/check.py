#!/usr/bin/env python3
"""Exhaustively evaluate the table and counter in all representable old phases."""
from itertools import product

def semantic(w):
    real = [x for x in w if x != "."]
    k = sum(x == y == "a" for x, y in zip(real, real[1:]))
    R = [next((x == "a" for x in w[j+1:] if x != "."), False) for j in range(len(w))]
    L = [next((x == "a" for x in w[j-1::-1] if x != "."), False) if j else False
         for j in range(len(w))]
    return L, R, k

def startup(n):
    return [False]*n, [False]*n, True, [False]*n, True, True

def step(w,i,v,state):
    Lp,Rp,np,C,cp,Q = state
    u = w[i]
    w1 = w[:i]+(v,)+w[i+1:]
    n = len(w)
    ne = [False]*n
    nnew = v=="b" or (v=="." and u!="b")
    def lens(P,j):
        return P[j] if np else not P[j]
    def upd(P, sign):
        ans = ne.copy()
        for x in range(n):
            p,m = lens(P,x),lens(P,i)
            sites = range(min(i,x)+1,max(i,x))
            ia = any(w1[y]=="a" for y in sites)
            ib = any(w1[y]=="b" for y in sites)
            outside = sign*(i-x)<=0
            if v=="a": ans[x] = not p and (outside or ib)
            elif v=="b": ans[x] = p and (outside or ia)
            elif u=="a": ans[x] = p and (outside or m or ia)
            elif u=="b": ans[x] = not p and (outside or not m or ib)
            else: ans[x]=p
        return ans
    L1,R1=upd(Lp,-1),upd(Rp,+1)
    a,b=lens(Lp,i),lens(Rp,i)
    def f(c):
        return int(a)+int(b) if c=="a" else int(a and b) if c=="." else 0
    delta=f(v)-f(u)
    T=[x if cp else not x for x in C]
    if delta<0:
        cp1=True
        C1=[sum(T[x+1:])>=-delta for x in range(n)]
    elif delta>0:
        cp1=False
        C1=[sum(not y for y in T[:x])>=delta for x in range(n)]
    else:
        cp1=True
        C1=T
    Q1=(delta==0 and Q) or (delta==-1 and n>=2 and not T[1]) or (delta==-2 and n>=3 and not T[2])
    return w1,(L1,R1,nnew,C1,cp1,Q1)

def verify(w,state):
    L,R,k=semantic(w)
    Lp,Rp,np,C,cp,Q=state
    assert [x==np for x in Lp]==L
    assert [x==np for x in Rp]==R
    assert [x==cp for x in C]==[x<k for x in range(len(w))]
    assert Q==(k==0)

def main():
    nsteps=0
    for n in range(8):
        verify((".",)*n,startup(n))
        for w in product(".ab",repeat=n):
            L,R,k=semantic(w)
            for np,cp in product((False,True),repeat=2):
                data=([x==np for x in L],[x==np for x in R],np,
                      [(x<k)==cp for x in range(n)],cp,k==0)
                verify(w,data)
                for i in range(n):
                    for v in ".ab":
                        verify(*step(w,i,v,data))
                        nsteps+=1
    print(f"PASS: {nsteps} exhaustive literal transitions, n=0..7, both old polarity bits arbitrary.")
if __name__=="__main__":
    main()
