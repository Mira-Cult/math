#!/usr/bin/env python3
"""Exact connected width-two triple-factor Boolean scope witness."""
import argparse
from fractions import Fraction
from itertools import combinations


def v(s):
    a,b,c,d=((s>>i)&1 for i in range(4))
    return 3-2*a-2*b-c+a*b+b*c+c*d


def base_truth():
    lengths={s:4-v(s) for s in range(16)}
    allocation={};cursor=0
    for s,d in sorted(lengths.items(),key=lambda it:(it[1],it[0])):
        width=4**(4-d)
        assert cursor%width==0
        for z in range(cursor,cursor+width):allocation[z]=(s,8-2*d)
        cursor+=width
    assert cursor==256
    return [(-1)**(((s&x).bit_count())+sum(((z>>j)&1)*((z>>(j+1))&1) for j in range(0,q,2)))
            for z in range(256) for s,q in [allocation[z]] for x in range(16)]


def walsh(vals):
    out=list(vals);step=1
    while step<len(out):
        for start in range(0,len(out),2*step):
            for j in range(start,start+step):
                a,b=out[j],out[j+step];out[j],out[j+step]=a+b,a-b
        step*=2
    return out


def core_old(s,m):
    out=s
    for i in range(m-1):
        if (s>>(4*(i+1)))&1:out^=1<<(4*i+1)
    return out


def bags_graph(m):
    edges=set();bags=[];links=[]
    last=None
    for i in range(m):
        a,b,c,d=range(4*i,4*i+4)
        if i<m-1:
            nxt=4*(i+1)
            block=[{a,b,nxt},{b,c,nxt},{c,d}]
        else:block=[{a,b},{b,c},{c,d}]
        start=len(bags);bags.extend(block)
        links.extend([(start,start+1),(start+1,start+2)])
        if last is not None:links.append((last,start))
        last=start+1
        for bag in block:
            edges.update(tuple(sorted(e)) for e in combinations(bag,2))
    assert len(links)==len(bags)-1
    for j in range(4*m):
        ids={i for i,b in enumerate(bags) if j in b};seen=set();stack=[next(iter(ids))]
        while stack:
            a=stack.pop()
            if a in seen:continue
            seen.add(a)
            stack.extend(b if a==c else c for b,c in links if a in (b,c) and (b if a==c else c) in ids)
        assert seen==ids
    return edges


def forest(n,edges,deleted):
    parent=list(range(n))
    def root(a):
        while parent[a]!=a:a=parent[a]
        return a
    for a,b in edges:
        if a in deleted or b in deleted:continue
        ra,rb=root(a),root(b)
        if ra==rb:return False
        parent[ra]=rb
    return True


def check():
    truth=base_truth();assert len(truth)==4096 and set(truth)=={-1,1}
    W=walsh(truth)
    for s,a in enumerate(W):assert abs(a)==2**(4+v(s&15))
    q=[Fraction(sum(4**v(s) for s in range(16) if (s>>i)&1),256) for i in range(4)]
    assert q==[Fraction(5,64),Fraction(35,256),Fraction(55,128),Fraction(161,256)]
    for m in range(1,5):
        vals=[sum(v((core_old(s,m)>>(4*i))&15) for i in range(m)) for s in range(1<<(4*m))]
        weights=[4**z for z in vals];Z=sum(weights);assert Z==256**m
        # Shift all d bits, exactly as in the note.
        shift=sum(1<<(4*i+3) for i in range(m))
        H=Fraction(sum(w*(8*m-2*z) for w,z in zip(weights,vals)),Z)+8*m
        I=Fraction(sum(w*(s^shift).bit_count() for s,w in enumerate(weights)),Z)+4*m
        assert H==Fraction(345*m,32)
        assert I==Fraction(321*m,64)+Fraction(465*(m-1),8192)
        # Ordinary integer Mobius coefficients of log-amplitude energy.
        poly=vals[:]
        for bit in range(4*m):
            for s in range(1<<(4*m)):
                if (s>>bit)&1:poly[s]-=poly[s^(1<<bit)]
        for i in range(m-1):
            for tri in [(4*i,4*i+1,4*(i+1)),(4*i+1,4*i+2,4*(i+1))]:
                assert poly[sum(1<<j for j in tri)]==-2
        assert all(s.bit_count()<=3 or a==0 for s,a in enumerate(poly))
        edges=bags_graph(m);cut={4*i+1 for i in range(m-1)}
        assert forest(4*m,edges,cut)
        triples=[{4*i+1,4*i+2,4*(i+1)} for i in range(m-1)]
        assert len(set().union(*triples))==3*(m-1)
        print({'m':m,'core_states':len(vals),'H':str(H),'I':str(I),'feedback_vertex_number':m-1})
    print('All exact standard-library checks passed.')
    return truth,W


def full_two_block(truth,W):
    import numpy as np
    base=np.asarray(truth,dtype=np.int32);w=np.asarray(W,dtype=np.int32)
    n=24;size=1<<n;freq=np.arange(size,dtype=np.uint32)
    s1=freq&4095;s2=freq>>12
    # Physical shear a_2 <- a_2 xor b_1.
    transformed2=s2^((s1>>1)&1)
    a=base[s1]*base[transformed2]
    assert a.min()==-1 and a.max()==1
    del transformed2
    step=1
    while step<size:
        view=a.reshape(-1,2,step)
        first=view[:,0,:].copy()
        view[:,0,:]+=view[:,1,:]
        view[:,1,:]=first-view[:,1,:]
        step*=2
    # Spectral inverse transpose b_1 <- b_1 xor a_2.
    old1=s1^((s2&1)<<1)
    expected=w[old1]*w[s2]
    assert np.array_equal(a,expected)
    assert np.all(a!=0)
    assert int(np.sum(a.astype(np.int64)**2))==size*size
    print('All 16,777,216 signed Walsh coefficients of the 24-bit Boolean witness checked exactly.')


if __name__=='__main__':
    args=argparse.ArgumentParser();args.add_argument('--full-two-block',action='store_true');opt=args.parse_args()
    truth,W=check()
    if opt.full_two_block:full_two_block(truth,W)
