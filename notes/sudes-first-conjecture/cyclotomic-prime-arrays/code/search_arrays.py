#!/usr/bin/env python3
"""Seeded finite search; failure to find an array is not an obstruction."""
import argparse
import json
import math
import random
from pathlib import Path
from cyclotomic import Field, lines, certificate, add, sub


def search(m,n,D,seed,steps,restarts):
    f=Field(m)
    pool,_=f.pool(n**D)
    ls=lines(n,D)
    inc=[set() for _ in pool]
    for j,line in enumerate(ls):
        for i in line:
            inc[i].add(j)
    rng=random.Random(seed)
    best=len(ls)+1
    for restart in range(restarts):
        a=pool[:]
        rng.shuffle(a)
        sums=[tuple(sum(a[i][k] for i in line) for k in range(4)) for line in ls]
        bad=[f.prime_certificate(s) is None for s in sums]
        score=sum(bad)
        for step in range(steps+1):
            if score<best:
                best=score
            if score==0:
                return certificate(f,n,D,a,{'method':'seeded-swap-annealing',
                    'seed':seed,'steps_per_restart':steps,'restarts_budget':restarts,
                    'restart':restart,'successful_step':step}), best
            failures=[j for j,b in enumerate(bad) if b]
            i=rng.choice(ls[rng.choice(failures)])
            j=rng.randrange(len(pool))
            if i==j:
                continue
            delta=sub(a[j],a[i])
            affected=inc[i]^inc[j]
            changed={k:add(sums[k],delta) if k in inc[i] else sub(sums[k],delta)
                     for k in affected}
            new_bad={k:f.prime_certificate(s) is None for k,s in changed.items()}
            diff=sum(new_bad[k]-bad[k] for k in affected)
            # Repeated deterministic cooling cycles help escape small local minima.
            temperature=0.10+0.70*(1-(step%5000)/5000)
            if diff<=0 or rng.random()<math.exp(-diff/temperature):
                a[i],a[j]=a[j],a[i]
                for k,s in changed.items():
                    sums[k],bad[k]=s,new_bad[k]
                score+=diff
        print(json.dumps({'m':m,'n':n,'D':D,'restart':restart,'best_bad':best}),flush=True)
    return None,best


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--m',type=int,choices=(5,8,12),required=True)
    p.add_argument('--n',type=int,required=True)
    p.add_argument('--D',type=int,choices=(2,3),default=2)
    p.add_argument('--seed',type=int,default=20261102)
    p.add_argument('--steps',type=int,default=100000)
    p.add_argument('--restarts',type=int,default=20)
    p.add_argument('--output',required=True)
    a=p.parse_args()
    cert,best=search(a.m,a.n,a.D,a.seed,a.steps,a.restarts)
    if cert is None:
        print(json.dumps({'status':'budget-exhausted-not-a-proof','best_bad':best}))
        return 1
    Path(a.output).write_text(json.dumps(cert,indent=2)+'\n')
    print(json.dumps({'status':'found','output':a.output,'lines':len(cert['lines']),
                      'metadata':cert['metadata']}))
    return 0


if __name__=='__main__':
    raise SystemExit(main())
