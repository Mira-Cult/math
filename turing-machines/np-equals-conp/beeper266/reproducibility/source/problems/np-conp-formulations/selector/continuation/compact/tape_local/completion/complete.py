"""Complete and merge a partial table whose holes are proved unreachable.

This is a separate admitted-execution refinement of the immutable 407 control.
It never treats a reached row as a don't-care. Every retained row must preserve
write, move, event and the supplied quotient relation. The holes are exactly
the inherited explicit totalization requests (plus their unreachable sink).
"""
from pathlib import Path
from collections import defaultdict, deque
import argparse
import hashlib
import json
import random

HERE = Path(__file__).resolve().parent
CONTROL = HERE.parents[1]/'native/machines/selected'
EXPECTED = 'c30aad560971733010956bad993801ce8bfa15e29706be18c47ec306d41afae2'
CONTROL_HASHES = {
    'events.tm': EXPECTED,
    'raw.tm': 'cbe5f4461f3d421c78b1f27301a29ea2c1a098a0982cd3244b97b02759842e4d',
    'machine.tm': 'cc50ec777e55ef5c6cef3edcb0c928e2bb2ab4983b756bfb864a78d253467658',
    'names.json': 'cbb6ad72b3d911e311180e5ef249bdc88eab6e24ed53e9a840b6fbdf987170e3',
    'quotient.json': '2778fe1163d52e668d7fd547924df3f83f9ec0752bc15f8e896a910b8391ad38',
    'event-quotient.json': '290a3619a36815f214d35631cf05348bbecb2e6116d729519b9623e6f835a4dd',
    'selector.json': 'baf77154f37e5c7b1c5e04e1ce8e34f31e0123a6fb478205f49cfcad784f951b',
}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(convention='events'):
    assert convention in ('events','B')
    for name,digest in CONTROL_HASHES.items():
        assert sha(CONTROL/name)==digest,('changed pinned control input',name)
    names = json.loads((CONTROL/'names.json').read_text())
    quotient = json.loads((CONTROL/'quotient.json').read_text())
    event = json.loads((CONTROL/'event-quotient.json').read_text())['mapping']
    requests = json.loads((CONTROL/'selector.json').read_text())['new_totalized_rows']
    rawmap = {q:(event[quotient[str(q)]] if convention=='events' else quotient[str(q)])
              for q in names.values()}
    requested = {(names[name],int(bit)) for name,bit in requests if name in names}
    requested.update((names['silent.sink'],bit) for bit in (0,1))
    preimage = defaultdict(list)
    for q in names.values():
        preimage[rawmap[q]].append(q)
    holes = {(q,bit) for q,group in preimage.items() for bit in (0,1)
             if all((old,bit) in requested for old in group)}
    rows = {}
    filename='events.tm' if convention=='events' else 'machine.tm'
    for line in (CONTROL/filename).read_text().splitlines():
        if line.startswith('#') or not line.strip():
            continue
        if convention=='events':q,read,write,move,target,mark=line.split()
        else:
            q,read,write,move,target=line.split();mark=int(q=='1')
        rows[int(q),int(read)]=(int(write),move,int(target),int(mark))
    n=407 if convention=='events' else 408
    assert len(rows)==2*n and set(q for q,_ in rows)==set(range(n))
    sink=rawmap[names['silent.sink']]
    assert all(rows[q,b][2]==sink for q,b in holes)
    return rows,holes,dict(format='np-conp-unreachable-totalization-domain-v1',
        control_sha256=sha(CONTROL/filename), convention=convention,
        source_request_file_sha256=sha(CONTROL/'selector.json'),
        requests=requests,raw_to_events=rawmap,
        event_holes=[list(k) for k in sorted(holes)],sink=sink,
        preimages={str(q):preimage[q] for q,_ in sorted(holes)},
        premise='the inherited source/primitive/bootstrap composition proves no requested row is reached; consequently its sink is never reached')


def compatible_pairs(rows,holes):
    n=len(rows)//2
    depend=defaultdict(list)
    bad=set();queue=deque()
    for a in range(n):
        for b in range(a+1,n):
            pair=a*n+b
            for bit in (0,1):
                if (a,bit) in holes or (b,bit) in holes:
                    continue
                x,y=rows[a,bit],rows[b,bit]
                if (x[0],x[1],x[3])!=(y[0],y[1],y[3]):
                    if pair not in bad:bad.add(pair);queue.append(pair)
                elif x[2]!=y[2]:
                    lo,hi=sorted((x[2],y[2]));depend[lo*n+hi].append(pair)
    while queue:
        for pair in depend[queue.popleft()]:
            if pair not in bad:bad.add(pair);queue.append(pair)
    return [(a,b) for a in range(n) for b in range(a+1,n) if a*n+b not in bad]


class Partition:
    def __init__(self,rows,holes):
        n=len(rows)//2
        self.parent=list(range(n))
        self.data=[[None if (q,b) in holes else rows[q,b] for b in (0,1)]
                   for q in range(n)]
        self.count=n

    def root(self,q):
        while self.parent[q]!=q:q=self.parent[q]
        return q

    def merge(self,a,b):
        parent=self.parent.copy();data=[x.copy() for x in self.data];count=self.count
        todo=[(a,b)]
        while todo:
            a,b=map(self.root,todo.pop())
            if a==b:continue
            if a>b:a,b=b,a
            for bit in (0,1):
                x,y=self.data[a][bit],self.data[b][bit]
                if x is not None and y is not None:
                    if (x[0],x[1],x[3])!=(y[0],y[1],y[3]):
                        self.parent,self.data,self.count=parent,data,count
                        return False
                    todo.append((x[2],y[2]))
                elif x is None:self.data[a][bit]=y
            self.parent[b]=a;self.count-=1
        return True

    def mapping(self):
        roots=sorted({self.root(q) for q in range(len(self.parent))})
        number={q:i for i,q in enumerate(roots)}
        return [number[self.root(q)] for q in range(len(self.parent))]


def validate(rows,holes,mapping):
    assert len(mapping)==len(rows)//2 and all(type(x) is int and x>=0 for x in mapping)
    count=max(mapping)+1
    assert set(mapping)==set(range(count)) and mapping[0]==0
    final={}
    for (q,bit),(w,d,t,e) in rows.items():
        if (q,bit) in holes:continue
        key=mapping[q],bit;value=w,d,mapping[t],e
        if key in final:assert final[key]==value,('incompatible retained rows',q,bit)
        final[key]=value
    for q in range(count):
        for bit in (0,1):
            final.setdefault((q,bit),(bit,'R',q,0))
    assert len(final)==2*count
    return final


def emit(rows,path,beep=None):
    count=len(rows)//2
    if beep is None:
        text=f'#! format beeper-events-v1\n#! states {count}\n#! start 0\n#! blank 0\n#! head 0\n'
        text+=''.join(f'{q} {b} {w} {d} {t} {e}\n' for (q,b),(w,d,t,e) in sorted(rows.items()))
    else:
        assert all(e==int(q==beep) for (q,_),(_,_,_,e) in rows.items())
        text=f'#! format beeper-v1\n#! states {count}\n#! start 0\n#! beep {beep}\n#! blank 0\n#! head 0\n'
        text+=''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t,_) in sorted(rows.items()))
    Path(path).write_text(text)


def run(out,plan=None,rounds=64,convention='events'):
    out=Path(out)
    if out.exists():raise ValueError('fresh output required')
    rows,holes,domain=load(convention)
    if plan is None:
        pairs=compatible_pairs(rows,holes);best=None;trials=[]
        for seed in range(rounds):
            order=pairs.copy()
            if seed:random.Random(seed).shuffle(order)
            part=Partition(rows,holes)
            for a,b in order:part.merge(a,b)
            mapping=part.mapping();validate(rows,holes,mapping)
            trials.append(dict(seed=seed,states=part.count))
            if best is None or part.count<best[0]:best=part.count,mapping,seed
        result=dict(mapping=best[1],selected_seed=best[2],trials=trials,
                    compatible_pairs=len(pairs),search_scope='deterministic bounded greedy congruence completion; no global minimum')
    else:
        result=json.loads(Path(plan).read_text())
        assert result['format']=='np-conp-partial-completion-v1'
        assert result['control_sha256']==domain['control_sha256']
        assert result['convention']==convention
        assert result['holes']==[list(x) for x in sorted(holes)]
    final=validate(rows,holes,result['mapping'])
    if convention=='B':
        assert all((q==1)==(target==result['mapping'][1]) for q,target in enumerate(result['mapping']))
    out.mkdir(parents=True)
    filename='events.tm' if convention=='events' else 'machine.tm'
    emit(final,out/filename,beep=result['mapping'][1] if convention=='B' else None)
    if plan is not None:
        assert result['states']==len(final)//2 and result['rows']==len(final)
        assert result['table_sha256']==sha(out/filename)
    result.update(format='np-conp-partial-completion-v1',control_sha256=domain['control_sha256'],
                  convention=convention,
                  holes=[list(x) for x in sorted(holes)],states=len(final)//2,
                  rows=len(final),table_sha256=sha(out/filename))
    (out/'plan.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    (out/'domain.json').write_text(json.dumps(domain,sort_keys=True,indent=2)+'\n')
    return {k:result[k] for k in ('states','rows','table_sha256')}


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--plan',type=Path);parser.add_argument('--rounds',type=int,default=64)
    parser.add_argument('--convention',choices=('events','B'),default='events')
    args=parser.parse_args();print(json.dumps(run(args.out,args.plan,args.rounds,args.convention),indent=2))
