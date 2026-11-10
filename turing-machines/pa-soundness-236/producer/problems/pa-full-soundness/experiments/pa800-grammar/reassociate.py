#!/usr/bin/env python3
"""Deterministic, finite, source-transparent PA804 -> PA800 grammar refactoring.

Dependency: the neighboring frozen pa804-continuation checkpoint. This pass
changes only the right/left association of compiled binary control nodes. All
primitive leaves and branch targets (including zero tests and loop restarts)
are exhaustively compared against that frozen producer.
"""
from __future__ import annotations
import sys,json,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
PA804=HERE.parent/'pa804-continuation'
if not PA804.is_dir():
    raise RuntimeError(f'PA804 recovery folder missing: {PA804}')
sys.path.insert(0,str(PA804))
import optimize as opt
import grammar_search as gs
import build_selected

PLAN=HERE/'plan.json'

def rotate(builder,pattern):
    direction,a,c=pattern
    intern=gs.interner(builder)
    matches=[]
    if direction=='R':
        for i in sorted(builder.reachable()):
            x,y=builder.sequences[i].seq
            if x==a and isinstance(y,int):
                v,w=builder.sequences[y].seq
                if v==c:matches.append((i,w))
        if not matches:raise ValueError(('unmatched right rotation',pattern))
        inner=intern(a,c)
        for i,z in matches:builder.sequences[i].seq=(inner,z)
    elif direction=='L':
        for i in sorted(builder.reachable()):
            x,y=builder.sequences[i].seq
            if y==c and isinstance(x,int):
                v,w=builder.sequences[x].seq
                if w==a:matches.append((i,v))
        if not matches:raise ValueError(('unmatched left rotation',pattern))
        inner=intern(a,c)
        for i,z in matches:builder.sequences[i].seq=(z,inner)
    else:
        raise ValueError(('unknown rotation direction',direction))
    return len(matches)

class PA800(build_selected.ReassociatedOneStack):
    def build_tree(self):
        super().build_tree()
        before=gs.graph(self)
        plan=json.loads(PLAN.read_text())
        for pattern in plan['moves']:rotate(self,pattern)
        self.name_sequences()
        after=gs.graph(self)
        if after!=before:raise AssertionError(('control graph changed',gs.diff(before,after)))
        root,measures=opt.build.dag_measures(self)
        if (len(list(self.reachable())),*measures[root][::-1])!=tuple(plan['metric']):
            raise AssertionError('selected grammar size/depth does not match pinned plan')
        return self

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--out',required=True,type=Path);a=p.parse_args()
    _,l,_=opt.compile_candidate(PA800,a.out)
    print(json.dumps(l,indent=2))
