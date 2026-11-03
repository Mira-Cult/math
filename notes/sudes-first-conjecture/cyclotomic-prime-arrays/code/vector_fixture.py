#!/usr/bin/env python3
"""Four arithmetic directions in one actual whole-element cuboid permutation.

This is a physical trade fixture, NOT an all-prime-line array. Verification
uses the independent checker's arithmetic and full-line enumeration.
"""
import argparse
import copy
import hashlib
import itertools
import json
from pathlib import Path


def digest(obj):
    return hashlib.sha256(json.dumps(obj,separators=(',',':')).encode()).hexdigest()


def idx(point,n):
    x,y,z=point
    return (x*n+y)*n+z


def generate(m):
    from cyclotomic import Field,add
    f=Field(m)
    n=9
    pool,completeness=f.pool(n**3)
    bank=set(pool)
    used=set()
    stages=[]
    for j in range(4):
        gap=tuple(2 if k==j else 0 for k in range(4))
        pairs=[]
        for p in pool:
            q=add(p,gap)
            if p not in used and q not in used and q in bank:
                pairs.append([list(p),list(q)])
                used.update((p,q))
                if len(pairs)==4:
                    break
        if len(pairs)!=4:
            raise RuntimeError('insufficient actual pairs for fixed fixture gap')
        a,b,c,d=j,(j+1)%4,(j+2)%4,(j+3)%4
        stages.append({'gap':list(gap),'axes':[[a,b],[a,c],[a,d]],
                       'pairs':pairs,'residue_mod_2':[0,0,0,0]})
    result={'format':'cyclotomic-four-direction-cuboid-v1','conductor':m,
            'dimension':3,'side':n,'normalization':'balanced-log-symmetric-sector-v1',
            'pool':[list(p) for p in pool], 'pool_completeness':completeness,
            'stages':stages,'lattice_index':16,
            'claim':'physical trades only; no all-prime-line assertion'}
    # Produce records independently from the verifier's checks below.
    from cyclotomic import lines
    ls=lines(n,3)
    result['required_lines']=[list(line) for line in ls]
    records=[]
    for mask in range(16):
        a=build_array(result,mask)
        sums=[[sum(a[i][j] for i in line) for j in range(4)] for line in ls]
        records.append({'mask':mask,'array_sha256':digest(a),'line_sums_sha256':digest(sums),
                        'native_body_sum':[sum(a[idx((t,t,t),n)][j] for t in range(n))
                                           for j in range(4)]})
    result['orientations']=records
    return result


def build_array(data,mask):
    n=data['side']
    a=[None]*(n**3)
    used=set()
    for j,stage in enumerate(data['stages']):
        axes=stage['axes']
        for k,(v,w) in enumerate(itertools.product(range(2),repeat=2)):
            p,q=map(tuple,stage['pairs'][k])
            left,right=(p,q) if (v+w)%2==0 else (q,p)
            if mask>>j&1:
                left,right=right,left
            for u,value in enumerate((left,right)):
                cell=idx((axes[0][u],axes[1][v],axes[2][w]),n)
                if a[cell] is not None or value in used:
                    raise ValueError('overlapping supports or repeated endpoints')
                a[cell]=value;used.add(value)
    filler=iter(tuple(p) for p in data['pool'] if tuple(p) not in used)
    for i in range(len(a)):
        if a[i] is None:
            a[i]=next(filler)
    if next(filler,None) is not None:
        raise ValueError('unused filler')
    return a


def verify(data):
    from check_certificate import ExactField,all_lines,determinant,require
    require(data['format']=='cyclotomic-four-direction-cuboid-v1','wrong fixture format')
    f=ExactField(data['conductor']);n=data['side']
    require(n==9 and data['dimension']==3,'wrong fixture geometry')
    require(data['normalization']=='balanced-log-symmetric-sector-v1','wrong pool model')
    require(data['claim']=='physical trades only; no all-prime-line assertion','wrong claim')
    comp=data['pool_completeness'];B=comp['norm_cutoff']
    full=list(map(tuple,comp['all_through_cutoff']))
    keys=[]
    for p in full:
        rec=f.prime_record(p)
        require(f.normalized(p) and rec is not None,'noncanonical or nonprime input')
        require(rec['rational_prime'] not in f.omitted and rec['norm']<=B,'wrong cutoff class')
        keys.append((rec['rational_prime'],tuple(rec['quotient_polynomial'])))
    require(len(keys)==len(set(keys))==f.ideal_count(B)==comp['complete_tie_count'],
            'incomplete ideal pool or duplicate associates')
    full.sort(key=lambda p:(f.norm(p),p))
    pool=list(map(tuple,data['pool']))
    require(pool==full[:n**3] and f.norm(pool[-1])==B,'wrong initial pool')
    require(len(data['stages'])==4,'missing arithmetic direction')
    gaps=[s['gap'] for s in data['stages']]
    det=abs(determinant([[gaps[j][i] for j in range(4)] for i in range(4)]))
    require(det==16==data['lattice_index'],'dependent or wrong gap lattice')
    endpoints=[]
    for stage in data['stages']:
        require(len(stage['pairs'])==4,'cuboid needs four equal-gap pairs')
        require(stage['residue_mod_2']==[x%2 for x in stage['gap']]==[0]*4,
                'wrong residue or contained ideal')
        require(len(stage['axes'])==3 and all(len(x)==2 and len(set(x))==2
                    and all(type(v) is int and 0<=v<n for v in x) for x in stage['axes']),
                'invalid cuboid support')
        for p,q in stage['pairs']:
            require(tuple(q[k]-p[k] for k in range(4))==tuple(stage['gap']),
                    'not equal actual gaps')
            require(tuple(p) in pool and tuple(q) in pool,'pair outside exact pool')
            endpoints.extend((tuple(p),tuple(q)))
    require(len(endpoints)==len(set(endpoints))==32,'shared endpoints')
    ls=all_lines(n,3)
    require(data['required_lines']==[list(line) for line in ls] and len(ls)==301,
            'missing signed line')
    base=build_array(data,0)
    require(sorted(base)==sorted(pool),'base is not pool bijection')
    baseline=[tuple(sum(base[i][j] for i in line) for j in range(4)) for line in ls]
    native=tuple(idx((t,t,t),n) for t in range(n))
    native_index=ls.index(native)
    axis_indices=[];body_indices=[]
    for k,line in enumerate(ls):
        points=[(i//(n*n),(i//n)%n,i%n) for i in line]
        varying=sum(len({p[j] for p in points})>1 for j in range(3))
        if varying==1:axis_indices.append(k)
        if varying==3:body_indices.append(k)
    require(len(body_indices)==4 and len(axis_indices)==3*n*n,'wrong independent line types')
    require(len(data['orientations'])==16,'missing orientation')
    for mask,record in enumerate(data['orientations']):
        require(record['mask']==mask,'wrong orientation order')
        a=build_array(data,mask)
        require(sorted(a)==sorted(pool),'orientation is not same whole-element permutation')
        sums=[tuple(sum(a[i][j] for i in line) for j in range(4)) for line in ls]
        require(record['array_sha256']==digest(a) and record['line_sums_sha256']==digest(sums),
                'bad complete array or line-sum digest')
        require(record['native_body_sum']==list(sums[native_index]),'wrong native sum')
        change=tuple(sum(gaps[j][k] for j in range(4) if mask>>j&1) for k in range(4))
        require(tuple(sums[native_index][k]-baseline[native_index][k] for k in range(4))==change,
                'wrong four-coordinate native action')
        for k in axis_indices+body_indices:
            if k!=native_index:
                require(sums[k]==baseline[k],'axis or other body damaged')
        # Independently check the cuboid sign identity on every required line.
        for k,line in enumerate(ls):
            expected=[0]*4
            for j,stage in enumerate(data['stages']):
                if not mask>>j&1:
                    continue
                coef=0
                for bits in itertools.product(range(2),repeat=3):
                    cell=idx(tuple(stage['axes'][s][bits[s]] for s in range(3)),n)
                    if cell in line:
                        coef+=(-1)**sum(bits)
                for c in range(4):expected[c]+=coef*gaps[j][c]
            require(tuple(sums[k][c]-baseline[k][c] for c in range(4))==tuple(expected),
                    'wrong full line incidence signature')
    return {'m':f.m,'side':n,'pool_entries':len(pool),'required_lines':len(ls),
            'arithmetic_rank':4,'lattice_index':det,'actual_pairs':16,
            'orientations':16,'norm_cutoff':B,'all_prime_line_claim':False}


def negative_controls(data):
    mutations=[]
    d=copy.deepcopy(data);d['stages'][3]['gap']=d['stages'][0]['gap'];mutations.append(d)
    d=copy.deepcopy(data);d['lattice_index']=8;mutations.append(d)
    d=copy.deepcopy(data);d['stages'][0]['residue_mod_2'][0]=1;mutations.append(d)
    d=copy.deepcopy(data);d['stages'][1]['pairs'][0]=d['stages'][0]['pairs'][0];mutations.append(d)
    d=copy.deepcopy(data);d['stages'][0]['pairs'].pop();mutations.append(d)
    d=copy.deepcopy(data);d['required_lines'].pop();mutations.append(d)
    d=copy.deepcopy(data);d['orientations'].pop();mutations.append(d)
    d=copy.deepcopy(data);d['orientations'][1]['native_body_sum'][0]+=1;mutations.append(d)
    d=copy.deepcopy(data);d['pool_completeness']['all_through_cutoff'].pop();mutations.append(d)
    from check_certificate import ExactField
    f=ExactField(data['conductor'])
    d=copy.deepcopy(data);d['pool'][0]=list(f.multiply(tuple(d['pool'][0]),f.unit));mutations.append(d)
    for d in mutations:
        try:verify(d)
        except (ValueError,AssertionError,IndexError,StopIteration):pass
        else:raise AssertionError('corrupt physical fixture accepted')
    return len(mutations)


def main():
    p=argparse.ArgumentParser();p.add_argument('action',choices=('generate','verify'))
    p.add_argument('--m',type=int,choices=(5,8,12));p.add_argument('--output')
    p.add_argument('--negative-controls',action='store_true');p.add_argument('files',nargs='*')
    a=p.parse_args()
    if a.action=='generate':
        data=generate(a.m);summary=verify(data)
        Path(a.output).write_text(json.dumps(data,indent=2)+'\n');print(json.dumps(summary))
    else:
        for file in a.files:
            data=json.loads(Path(file).read_text());summary=verify(data)
            if a.negative_controls:summary['rejected_mutations']=negative_controls(data)
            print(json.dumps(summary))


if __name__=='__main__':main()
