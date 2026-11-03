#!/usr/bin/env python3
"""Independent replay of a two-colour obstruction on the full 3-cube.

Author: /root. No generator, arithmetic producer, or author replay imports.
Lines are reconstructed from opposite endpoint pairs. A supplied finite tree
is a proof: each force is justified by two equal known colours on a line,
each branch covers both colours of an unassigned cell, and every leaf gives
an actual monochromatic required line. Global colour exchange justifies the
single fixed central colour.
"""
import argparse
import copy
import hashlib
import itertools
import json
from pathlib import Path


class Invalid(ValueError):
    pass


def demand(condition, reason):
    if not condition:
        raise Invalid(reason)


def integer(value, low, high):
    return type(value) is int and low <= value <= high


def required_lines():
    points = list(itertools.product(range(3), repeat=3))
    index = {x:i for i,x in enumerate(points)}
    found = set()
    for a,b in itertools.combinations(points,2):
        differences = [b[j]-a[j] for j in range(3)]
        if not all(v in (-2,0,2) for v in differences):
            continue
        midpoint = tuple((a[j]+b[j])//2 for j in range(3))
        found.add(tuple(sorted((index[a],index[midpoint],index[b]))))
    demand(len(found)==49,'required-line reconstruction failed')
    return found


def verify(data):
    demand(data.get('format')=='full-signed-cube3-two-colour-unsat-v1','wrong certificate format')
    demand(data.get('side')==3 and data.get('dimension')==3 and data.get('colors')==2,'wrong finite model')
    demand(data.get('fixed_center')=={'cell':13,'color':0},'wrong colour-symmetry reduction')
    allowed = required_lines(); used = set()
    stats = {'nodes':0,'branches':0,'leaves':0,'forces':0,'maximum_depth':0}
    def line(value):
        demand(isinstance(value,list) and len(value)==3,'malformed line')
        demand(all(integer(x,0,26) for x in value),'invalid line cell')
        key = tuple(sorted(value))
        demand(key in allowed,'line is not a required full signed line')
        used.add(key)
        return key
    def visit(node, assignment, depth):
        demand(isinstance(node,dict),'node is not an object')
        stats['nodes']+=1;stats['maximum_depth']=max(stats['maximum_depth'],depth)
        demand(isinstance(node.get('forces'),list),'missing force list')
        current = assignment[:]
        for step in node['forces']:
            demand(isinstance(step,dict) and set(step)=={'line','cell','color'},'malformed force')
            support = line(step['line']); x=step['cell']; colour=step['color']
            demand(integer(x,0,26) and x in support,'forced cell not in line')
            demand(integer(colour,0,1),'invalid forced colour')
            demand(current[x] is None,'force overwrites assigned cell')
            others = [y for y in support if y!=x]
            demand(len(others)==2 and all(current[y]==1-colour for y in others),'force lacks two opposite-colour premises')
            current[x]=colour;stats['forces']+=1
        if 'conflict' in node:
            demand(set(node)=={'forces','conflict'},'malformed conflict leaf')
            support = line(node['conflict']); values=[current[x] for x in support]
            demand(values[0] in (0,1) and values.count(values[0])==3,'leaf line is not monochromatic')
            stats['leaves']+=1
            return
        demand(set(node)=={'forces','branch','children'},'malformed branch')
        x=node['branch'];children=node['children']
        demand(integer(x,0,26) and current[x] is None,'branch cell already assigned or invalid')
        demand(isinstance(children,list) and len(children)==2,'branch does not cover both colours')
        stats['branches']+=1
        for colour in range(2):
            child_assignment=current[:];child_assignment[x]=colour
            visit(children[colour],child_assignment,depth+1)
    values=[None]*27;values[13]=0
    visit(data.get('root'),values,0)
    demand(stats['leaves']==stats['branches']+1,'incomplete binary proof tree')
    return {'status':'verified-unsatisfiable','required_lines':len(allowed),'used_lines':len(used),**stats}


def nodes(root):
    yield root
    for child in root.get('children',[]):
        yield from nodes(child)


def negative_controls(original):
    tests=[]
    def test(name, mutate):
        data=copy.deepcopy(original);mutate(data)
        try:
            verify(data)
        except Invalid:
            tests.append(name)
        else:
            raise AssertionError('accepted corrupted proof: '+name)
    test('wrong_fixed_center',lambda d:d['fixed_center'].update(cell=12))
    test('missing_branch_colour',lambda d:d['root']['children'].pop())
    test('branch_on_assigned_center',lambda d:d['root'].update(branch=13))
    test('wrong_force_colour',lambda d:next(n for n in nodes(d['root']) if n['forces'])['forces'][0].update(color=1-next(n for n in nodes(d['root']) if n['forces'])['forces'][0]['color']))
    test('nonline_force',lambda d:next(n for n in nodes(d['root']) if n['forces'])['forces'][0].update(line=[0,1,4]))
    test('nonline_conflict',lambda d:next(n for n in nodes(d['root']) if 'conflict' in n).update(conflict=[0,1,4]))
    test('missing_conflict',lambda d:next(n for n in nodes(d['root']) if 'conflict' in n).pop('conflict'))
    test('forced_cell_outside_line',lambda d:next(n for n in nodes(d['root']) if n['forces'])['forces'][0].update(cell=27))
    return tests


def independent_search():
    """A separately implemented bounded 27-variable search, with no tree input."""
    lines=sorted(required_lines()); counts={'nodes':0,'conflicts':0}
    def solve(values):
        counts['nodes']+=1
        while True:
            changed=False
            for line in lines:
                seen={values[x] for x in line if values[x] is not None}
                if len(seen)==2:
                    continue
                remaining=[x for x in line if values[x] is None]
                if not remaining:
                    counts['conflicts']+=1
                    return None
                if len(remaining)==1:
                    values[remaining[0]]=1-next(iter(seen));changed=True
            if not changed:
                break
        candidates=[x for x in range(27) if values[x] is None]
        if not candidates:
            return values
        scores={x:0 for x in candidates}
        for line in lines:
            seen={values[x] for x in line if values[x] is not None}
            if len(seen)==2:
                continue
            for x in line:
                if values[x] is None:
                    scores[x]+=3 if seen else 1
        branch=max(candidates,key=lambda x:(scores[x],-x))
        for colour in (0,1):
            child=values[:];child[branch]=colour
            answer=solve(child)
            if answer is not None:
                return answer
        return None
    initial=[None]*27;initial[13]=0
    answer=solve(initial)
    demand(answer is None,'independent search found a coloring')
    return {'status':'independently-exhausted-unsatisfiable',**counts}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('certificate');parser.add_argument('--negative-controls',action='store_true');parser.add_argument('--independent-search',action='store_true');args=parser.parse_args()
    path=Path(args.certificate);raw=path.read_bytes();data=json.loads(raw)
    result=verify(data);result['sha256']=hashlib.sha256(raw).hexdigest()
    if args.negative_controls:
        result['rejected_negative_controls']=negative_controls(data)
    if args.independent_search:
        result['independent_search']=independent_search()
    print(json.dumps(result,sort_keys=True))


if __name__=='__main__':
    main()
