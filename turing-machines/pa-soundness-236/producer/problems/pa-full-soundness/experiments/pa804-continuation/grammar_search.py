#!/usr/bin/env python3
"""Finite all-branch primitive control-graph certificates for grammar refactoring.
The certificate checks every unfolded leaf and both DECNZ outcomes, not a trace.
"""
from __future__ import annotations
import argparse,copy,hashlib,json,time
from collections import Counter
from pathlib import Path
import optimize as opt
from TMBuilder import Sequence


def graph(builder):
    root=builder.find_seq('main().0'); leaves=[]; starts={}
    def visit(v,path):
        starts[path]=len(leaves)
        if type(v) is int:
            a,b=builder.sequences[v].seq
            visit(a,path+(0,));visit(b,path+(1,))
        else:leaves.append((path,v))
    visit(root,(1,1,0))
    def resolve(path):
        if path==(1,1) or path[:3]==(1,1,1):return 0
        return starts[path]
    def succ(path,k):
        for i in range(len(path)-1,1,-1):
            if path[i]==0:
                if k==0:return resolve(path[:i]+(1,))
                k-=1
        raise ValueError(('successor crosses sentinel',path,k))
    def restart(path,k):
        for i in range(len(path)-1,0,-1):
            if path[i]==1:
                if k==0:return resolve(path[:i+1])
                k-=1
        raise ValueError(('restart crosses sentinel',path,k))
    rows=[]
    for path,op in leaves:
        if op.startswith('_break.'):
            rows.append(('jump',succ(path,int(op.split('.')[1]))))
        elif op.startswith('_continue.'):
            rows.append(('jump',restart(path,int(op.split('.')[1]))))
        elif op.endswith('.decnz'):
            rows.append((op,succ(path,0),succ(path,1)))
        else:rows.append((op,succ(path,0)))
    return rows


def diff(a,b):
    if len(a)!=len(b):return {'kind':'leaf-count','old':len(a),'new':len(b)}
    for i,(x,y) in enumerate(zip(a,b)):
        if x!=y:return {'kind':'control-edge','leaf':i,'old':x,'new':y}
    return None


def digest(g):return hashlib.sha256(json.dumps(g,separators=(',',':')).encode()).hexdigest()


def interner(builder):
    lookup={tuple(s.seq):i for i,s in enumerate(builder.sequences)}
    def intern(a,b):
        key=(a,b)
        if key not in lookup:
            lookup[key]=len(builder.sequences);builder.sequences.append(Sequence(key))
        return lookup[key]
    return intern


def rotate(builder,pattern):
    """Globally rotate (a,(b,c)) to ((a,b),c) for the given exact a,b."""
    a,b=pattern;intern=interner(builder);matches=[]
    for i in sorted(builder.reachable()):
        x,right=builder.sequences[i].seq
        if x==a and type(right) is int:
            y,c=builder.sequences[right].seq
            if y==b:matches.append((i,c))
    if not matches:raise ValueError('pattern no longer occurs')
    new=intern(a,b)
    for i,c in matches:builder.sequences[i].seq=(new,c)
    return len(matches)


def candidates(builder):
    counts=Counter()
    for i in builder.reachable():
        a,right=builder.sequences[i].seq
        if type(right)is int:
            b,c=builder.sequences[right].seq;counts[a,b]+=1
    # Single-use rotations can create an already existing pair; include them.
    present={tuple(s.seq) for s in builder.sequences}
    return [p for p,n in sorted(counts.items(),key=lambda x:(-x[1],str(x[0])))
            if n>=2 or p in present]


def metric(b):
    # Primary grammar metric. Final physical selection is done by full build.
    root,m=opt.build.dag_measures(b)
    return len(list(b.reachable())),m[root]


def search(cls,seconds=30,max_accept=100):
    b=cls(opt.SOURCE);b.build_tree();original=graph(b);baseline=metric(b)
    accepts=[];rejected=[];tested=0;t0=time.monotonic()
    while time.monotonic()-t0<seconds and len(accepts)<max_accept:
        best=None;current=metric(b)
        for pat in candidates(b):
            if time.monotonic()-t0>=seconds:break
            c=copy.deepcopy(b);n=rotate(c,pat)
            m=metric(c)
            if m[0]>=current[0]:continue
            tested+=1
            try:d=diff(original,graph(c))
            except (ValueError,KeyError)as e:d={'kind':'invalid-control','message':str(e)}
            if d is not None:
                if len(rejected)<20:rejected.append({'pattern':pat,'mismatch':d})
                continue
            score=(m[0],m[1][1],m[1][0])
            if best is None or score<best[0]:best=(score,c,pat,n)
        if best is None:break
        score,b,pat,n=best
        accepts.append({'pattern':pat,'occurrences':n,'grammar':score[0]})
        print('accepted',len(accepts),score,pat,flush=True)
    b.name_sequences();assert diff(original,graph(b))is None
    return b,dict(format='all-branch-grammar-reassociation-v1',base_class=cls.__name__,
        source_sha256=hashlib.sha256(opt.SOURCE.encode()).hexdigest(),
        unfolded_leaves=len(original),graph_sha256=digest(original),baseline_metric=baseline,
        selected_metric=metric(b),transforms=accepts,tested_candidates=tested,
        rejected_examples=rejected,elapsed_seconds=time.monotonic()-t0)


def replay(cls,plan):
    b=cls(opt.SOURCE);b.build_tree();before=graph(b)
    assert digest(before)==plan['graph_sha256'] and len(before)==plan['unfolded_leaves']
    for t in plan['transforms']:rotate(b,t['pattern'])
    b.name_sequences();assert graph(b)==before
    return b

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--seconds',type=float,default=30);p.add_argument('--out',type=Path,required=True)
    args=p.parse_args();b,plan=search(opt.OneStack,args.seconds)
    args.out.write_text(json.dumps(plan,indent=2)+'\n')
    print(json.dumps({k:v for k,v in plan.items()if k not in ('transforms','rejected_examples')},indent=2))

class FactoredOneStack(opt.OneStack):
    def build_tree(self):
        self.main()
        self.breakout_common_subsequences()
        self.reduce_to_cons();self.name_sequences()
        return self
