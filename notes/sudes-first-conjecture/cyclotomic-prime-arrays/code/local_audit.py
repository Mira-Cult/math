#!/usr/bin/env python3
"""Exact cumulative residues and complete order-two obstruction witnesses."""
import argparse
import copy
import itertools
import json
from collections import Counter
from pathlib import Path


QUOTIENTS={
 5:[{'name':'inert_2_F16','p':2,'factor':[1,1,1,1,1]},
    {'name':'ramified_5_F5','p':5,'factor':[4,1]}],
 8:[{'name':'ramified_2_F2','p':2,'factor':[1,1]},
    {'name':'first_3_F9','p':3,'factor':[2,1,1]},
    {'name':'second_3_F9','p':3,'factor':[2,2,1]}],
12:[{'name':'ramified_2_F4','p':2,'factor':[1,1,1]},
    {'name':'ramified_3_F9','p':3,'factor':[1,0,1]}]}


def residue(a,q,fn):
    value=fn(list(a),q['factor'],q['p'])
    return tuple(value+[0]*(len(q['factor'])-1-len(value)))


def generate():
    from cyclotomic import Field,rem,add
    out={'format':'cyclotomic-local-ledger-v1','samples':[],'order_two_obstructions':[]}
    for m in (5,8,12):
        f=Field(m);maxpool,complete=f.pool(36)
        for M in (4,8,9,16,25,27,36):
            pool=maxpool[:M];B=f.norm(pool[-1])
            full=[a for a in complete['all_through_cutoff'] if f.norm(tuple(a))<=B]
            total=[sum(a[j] for a in pool) for j in range(4)]
            rows=[]
            for q in QUOTIENTS[m]:
                counts=Counter(residue(a,q,rem) for a in pool)
                rows.append({**q,'counts':[{'residue':list(b),'count':v}
                          for b,v in sorted(counts.items())],
                          'total_residue':list(residue(total,q,rem))})
            out['samples'].append({'m':m,'M':M,'norm_cutoff':B,'pool':pool,
                        'all_through_cutoff':full,'total':total,'quotients':rows})
        for D in (2,3):
            pool=maxpool[:2**D]
            pair=next((i,j) for i,j in itertools.combinations(range(len(pool)),2)
                      if f.prime_certificate(add(pool[i],pool[j])) is None)
            total=add(pool[pair[0]],pool[pair[1]])
            out['order_two_obstructions'].append({'m':m,'dimension':D,'side':2,
                'pool_indices':list(pair),'sum':list(total),'norm':f.norm(total),
                'reason':'every unordered pair of cells is a required full line at side two'})
    return out


def verify(data):
    from check_certificate import ExactField,polynomial_remainder,irreducible_small,all_lines,require
    require(data['format']=='cyclotomic-local-ledger-v1','wrong ledger format')
    require(len(data['samples'])==21 and len(data['order_two_obstructions'])==6,'missing sample')
    samples={}
    for s in data['samples']:
        f=ExactField(s['m']);M=s['M'];B=s['norm_cutoff']
        require((s['m'],M) not in samples,'duplicate sample')
        full=list(map(tuple,s['all_through_cutoff']));keys=[]
        for a in full:
            r=f.prime_record(a)
            require(r is not None and f.normalized(a),'noncanonical/nonprime ledger input')
            require(r['rational_prime'] not in f.omitted and r['norm']<=B,'wrong omitted class/cutoff')
            keys.append((r['rational_prime'],tuple(r['quotient_polynomial'])))
        require(len(keys)==len(set(keys))==f.ideal_count(B),'incomplete norm prefix')
        full.sort(key=lambda a:(f.norm(a),a));pool=list(map(tuple,s['pool']))
        require(pool==full[:M] and len(pool)==M and f.norm(pool[-1])==B,'wrong initial segment')
        total=[sum(a[j] for a in pool) for j in range(4)]
        require(total==s['total'],'incorrect exact cumulative total')
        require(len(s['quotients'])==len(QUOTIENTS[s['m']]),'missing local quotient')
        for q,template in zip(s['quotients'],QUOTIENTS[s['m']]):
            require(all(q[k]==v for k,v in template.items()),'wrong quotient')
            require(not polynomial_remainder(f.polynomial,q['factor'],q['p']) and
                    irreducible_small(q['factor'],q['p']),'quotient is not indicated residue field')
            cnt=Counter(residue(a,q,polynomial_remainder) for a in pool)
            expect=[{'residue':list(b),'count':v} for b,v in sorted(cnt.items())]
            require(q['counts']==expect,'wrong cumulative residue counts')
            actual=residue(total,q,polynomial_remainder)
            require(q['total_residue']==list(actual),'wrong total residue')
            aggregate=tuple(sum(b[j]*v for b,v in cnt.items())%q['p']
                            for j in range(len(q['factor'])-1))
            require(actual==aggregate,'aggregate identity failure')
        samples[s['m'],M]=(f,pool)
    require(set(samples)==set(itertools.product((5,8,12),(4,8,9,16,25,27,36))),
            'wrong sample inventory')
    seen=set()
    for o in data['order_two_obstructions']:
        m,D=o['m'],o['dimension'];require((m,D) not in seen,'duplicate obstruction');seen.add((m,D))
        f,pool=samples[m,2**D]
        ls=all_lines(2,D)
        require(set(ls)==set(itertools.combinations(range(2**D),2)),
                'side-two geometry not all pairs')
        i,j=o['pool_indices'];require(0<=i<j<len(pool),'wrong witness pair')
        total=tuple(pool[i][k]+pool[j][k] for k in range(4))
        require(list(total)==o['sum'] and f.norm(total)==o['norm'],'wrong obstruction sum')
        require(f.prime_record(total) is None,'obstruction pair is prime')
    require(seen==set(itertools.product((5,8,12),(2,3))),'missing obstruction dimension')
    return {'certified_prefixes':21,'certified_local_histograms':49,
            'complete_order_two_obstructions':6}


def main():
    p=argparse.ArgumentParser();p.add_argument('action',choices=('generate','verify'))
    p.add_argument('file');p.add_argument('--negative-controls',action='store_true');a=p.parse_args()
    if a.action=='generate':
        data=generate();result=verify(data);Path(a.file).write_text(json.dumps(data,indent=2)+'\n')
    else:data=json.loads(Path(a.file).read_text());result=verify(data)
    if a.negative_controls:
        tests=[]
        d=copy.deepcopy(data);d['samples'][0]['quotients'][0]['counts'][0]['count']+=1;tests.append(d)
        d=copy.deepcopy(data);d['samples'][0]['total'][0]+=1;tests.append(d)
        d=copy.deepcopy(data);d['samples'][0]['all_through_cutoff'].pop();tests.append(d)
        d=copy.deepcopy(data);d['order_two_obstructions'].pop();tests.append(d)
        d=copy.deepcopy(data);d['order_two_obstructions'][0]['norm']+=1;tests.append(d)
        for d in tests:
            try:verify(d)
            except (ValueError,AssertionError,IndexError,KeyError):pass
            else:raise AssertionError('corrupt ledger accepted')
        result['rejected_mutations']=len(tests)
    print(json.dumps(result))


if __name__=='__main__':main()
