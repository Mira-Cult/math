#!/usr/bin/env python3
"""Compiler-independent finite row and control-flow certificate checker.

Uses only the Python standard library. This is a separate implementation, not
an independently authored review and not an end-to-end proof-assistant result.
"""
from __future__ import annotations
import argparse,ast,hashlib,json
from collections import deque,defaultdict
from pathlib import Path
VENDOR_BLOB='f226ca44f524995fc7dcda108c50f94a07240582'

def table(path):
    h={};r={}
    for line in Path(path).read_text().splitlines():
        p=line.split()
        if not p:continue
        if p[0]=='#!':
            assert len(p)==3 and p[1] not in h;h[p[1]]=p[2];continue
        assert len(p)==6
        q,b,w,d,t,e=p
        assert all(str(int(v))==v for v in (q,b,w,t))
        q,b,w,t=map(int,(q,b,w,t));assert (q,b) not in r
        assert b in (0,1) and w in (0,1) and d in ('L','R') and e in ('-','0','1')
        r[q,b]=(w,d,t,e)
    assert set(h)=={'format','states','start','blank','head'}
    n=int(h['states']);assert h['format']=='bit-events-v1' and h['start']==h['blank']==h['head']=='0'
    assert set(r)=={(q,b) for q in range(n) for b in (0,1)}
    assert all(0<=t<n for w,d,t,e in r.values())
    return r

def grammar(m):
    g={int(k):tuple(v) for k,v in m['grammar'].items()};names={int(k):v for k,v in m['grammar_names'].items()}
    assert set(g)==set(names) and len(set(names.values()))==len(names)
    root=m['grammar_root'];assert names[root]=='main().0'
    rem={};parents=defaultdict(set)
    for i,vs in g.items():
        assert len(vs)==2
        cs=set(v for v in vs if type(v)is int)
        assert cs<=set(g);rem[i]=len(cs)
        for v in cs:parents[v].add(i)
    todo=deque(i for i in g if rem[i]==0);measure={}
    while todo:
        i=todo.popleft();a,b=g[i];ah,az=measure[a] if type(a)is int else (0,0);bh,bz=measure[b] if type(b)is int else(0,0)
        measure[i]=(1+max(ah,bh),max(az+1,bz))
        for p in parents[i]:
            rem[p]-=1
            if rem[p]==0:todo.append(p)
    assert len(measure)==len(g),'cyclic grammar'
    seen=set();todo=[root]
    while todo:
        i=todo.pop()
        if i in seen:continue
        seen.add(i);todo.extend(v for v in g[i] if type(v)is int)
    assert seen==set(g)
    assert measure[root]==(m['grammar_depth'],m['grammar_zero_depth'])
    return g,names,measure

def raw_expected(m,vendor):
    data=Path(vendor).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==VENDOR_BLOB
    parsed=ast.parse(data)
    literals=[ast.literal_eval(n.value) for n in parsed.body if isinstance(n,ast.Assign)
        and any(isinstance(t,ast.Name) and t.id=='framework' for t in n.targets)]
    assert len(literals)==1
    rows={}
    for line in literals[0].splitlines():
        if not line.strip() or line.startswith('#'):continue
        q,b,w,d,t=line.split();rows[q,int(b)]=(int(w),d,t,'-')
    g,names,metrics=grammar(m);regs=m['register_order'];assert regs and len(set(regs))==len(regs)
    for j,r in enumerate(regs):
        for op in ('inc','dec'):
            q=f'2b.reg.{j}.{op}';rows[q,0]=(0,'R',f'2b.reg.{j-1}.{op}','-');rows[q,1]=(1,'R',q,'-')
        inc,dec,nz=(f'3.{r}.{op}' for op in ('inc','dec','decnz'))
        rows[inc,0]=rows[nz,0]=(1,'R','1b.reg.prep_1','-')
        rows[inc,1]=(0,'R',f'2b.reg.{j}.inc','-');rows[nz,1]=(0,'R',f'2b.reg.{j}.dec','-')
        rows[dec,0]=(0,'R',nz,'-');rows[dec,1]=(0,'L','6.break.0','-')
    rows['0a.boot1.C',1]=(1,'R',f'3.{regs[0]}.inc','-')
    rows['0b.boot2.2',0]=(0,'R',f'3.{regs[0]}.inc','-')
    rows['0b.boot2.2',1]=(1,'R',f'3.{regs[0]}.decnz','-')
    depth=m['grammar_zero_depth']+2
    for k in range(1,depth+1):
        q=f'4.dispatch.{k}';rows[q,0]=(0,'L',f'4.dispatch.{k-1}','-');rows[q,1]=(1,'L',q,'-')
    rows['6.continue.0',1]=(1,'L',f'4.dispatch.{depth}','-')
    for i,vs in g.items():
        for side,v in enumerate(vs):
            if type(v)is int:row=(side,'R',names[v],'-')
            elif v.startswith('_break.'):
                k=int(v.split('.')[1]);assert k>=0
                if k==side==0:row=(1,'L','6.continue.0','-')
                else:
                    k-=1-side
                    for j in range(1,k+1):
                        rows[f'6.break.{j}',0]=(0,'L',f'6.break.{j-1}','-');rows[f'6.break.{j}',1]=(0,'L',f'6.break.{j}','-')
                    row=(0,'L',f'6.break.{k}','-')
            elif v.startswith('_continue.'):
                k=int(v.split('.')[1])-side;assert k>=0
                for j in range(1,k+1):
                    rows[f'6.continue.{j}',0]=(0,'L',f'6.continue.{j}','-');rows[f'6.continue.{j}',1]=(0,'L',f'6.continue.{j-1}','-')
                row=(0,'L',f'6.continue.{k}','-')
            else:
                assert v in ('emit.0','emit.1') or (v.startswith('3.') and (v,0)in rows)
                row=(side,'R',v,'-')
            rows[names[i],side]=row
    for bit in ('0','1'):
        rows['emit.'+bit,0]=(1,'R','1b.reg.prep_1','-');rows['emit.'+bit,1]=(0,'L','6.break.0',bit)
    init=m['initializer'];P=m['grammar_depth']+6;N=len(regs);length=P+2*N+2
    ones={0,1}|{P+2*i for i in range(N+1)}
    assert init==dict(padding=P,registers=N,max_leaf_path=m['grammar_depth']+3,
        initializer_states=length+4,entry='main().0',head=3,ones=sorted(ones))
    for pos in range(length):
        row=(int(pos in ones),'R',f'init.{pos+1}','-') if pos+1<length else (int(pos in ones),'L','init.scan','-')
        rows[f'init.{pos}',0]=rows[f'init.{pos}',1]=row
    rows['init.scan',0]=(0,'L','init.scan','-');rows['init.scan',1]=(1,'L','init.previous','-')
    rows['init.previous',0]=(0,'L','init.scan','-');rows['init.previous',1]=(1,'R','init.right1','-')
    for bit in (0,1):
        rows['init.right1',bit]=(bit,'R','init.right2','-');rows['init.right2',bit]=(bit,'R','main().0','-')
    seen=set();todo=['init.0'];missing=[]
    while todo:
        q=todo.pop()
        if q in seen:continue
        seen.add(q)
        for bit in (0,1):
            if (q,bit) in rows:todo.append(rows[q,bit][2])
            else:missing.append((q,bit))
    assert sorted(map(list,missing))==m['totalized_rows']
    if missing:
        seen.add('silent.sink')
        for q,bit in missing+[('silent.sink',0),('silent.sink',1)]:rows[q,bit]=(bit,'R','silent.sink','-')
    return {k:v for k,v in rows.items()if k[0]in seen}

def verify_named(rows,m,path):
    physical=table(path);ids=m['named_state_to_id'];assert set(ids)=={q for q,b in rows}
    assert set(ids.values())==set(range(len(physical)//2)) and ids['init.0']==0
    for (q,b),(w,d,t,e)in rows.items():assert physical[ids[q],b]==(w,d,ids[t],e),(q,b)
    data=Path(path).read_bytes();assert m['table_sha256']==hashlib.sha256(data).hexdigest() and m['table_bytes']==len(data)
    return physical

def quotient(raw,path,meta):
    selected=table(path);c=meta['quotient'];m=c['state_map']
    assert c['source_table_sha256']==hashlib.sha256((Path(path).parent.parent/'raw/machine.tm').read_bytes()).hexdigest()
    assert len(m)==len(raw)//2 and m[0]==0 and set(m)==set(range(len(selected)//2))
    for(q,b),(w,d,t,e)in raw.items():assert selected[m[q],b]==(w,d,m[t],e),(q,b)
    assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==meta['table_sha256']
    return len(raw)

def control_graph(m):
    """Independent iterative unfolding and prefix/successor reconstruction."""
    g,_,_=grammar(m);stack=[((1,1,0),m['grammar_root'])];starts={};leaves=[]
    while stack:
        p,n=stack.pop();starts[p]=len(leaves)
        if type(n)is int:
            a,b=g[n];stack.append((p+(1,),b));stack.append((p+(0,),a))
        else:leaves.append((p,n))
    def target(p):
        if p==(1,1) or p[:3]==(1,1,1):return 0
        return starts[p]
    def move(p,k,digit,restart=False):
        positions=[i for i in range(len(p)-1,0 if restart else 1,-1)if p[i]==digit]
        assert 0<=k<len(positions);i=positions[k]
        return target(p[:i+1] if restart else p[:i]+(1,))
    result=[]
    for p,op in leaves:
        if op.startswith('_break.'):r=['jump',move(p,int(op.split('.')[1]),0)]
        elif op.startswith('_continue.'):r=['jump',move(p,int(op.split('.')[1]),1,True)]
        elif op.endswith('.decnz'):r=[op,move(p,0,0),move(p,1,0)]
        else:r=[op,move(p,0,0)]
        result.append(r)
    return result

def check(root,parent,vendor):
    root=Path(root);p=root/'machine';cm=json.loads((p/'counted/raw/metadata.json').read_text())
    expected=raw_expected(cm,vendor);counted=verify_named(expected,cm,p/'counted/raw/machine.tm')
    count=quotient(counted,p/'counted/quotient/machine.tm',json.loads((p/'counted/quotient/metadata.json').read_text()))
    bootrows={k:v for k,v in expected.items()if not k[0].startswith('init.')}
    A,B,C,D,E='init.0','init.boot.B','init.boot.C','init.boot.D','init.boot.E';r=cm['register_order'][0]
    for q,b,w,d,t in[(A,0,1,'R',B),(A,1,1,'L',C),(B,0,0,'L',A),(B,1,0,'L',D),
       (C,0,1,'L',A),(C,1,1,'R',f'3.{r}.inc'),(D,0,1,'L',B),(D,1,1,'R',E),(E,0,0,'R',D),(E,1,0,'R',B)]:bootrows[q,b]=(w,d,t,'-')
    bm=json.loads((p/'boot/raw/metadata.json').read_text())
    assert cm['register_order']==bm['register_order'] and cm['grammar']==bm['grammar']
    assert cm['initializer']['max_leaf_path']<3822 and len(cm['register_order'])<=1909
    boot=verify_named(bootrows,bm,p/'boot/raw/machine.tm')
    count+=quotient(boot,p/'boot/quotient/machine.tm',json.loads((p/'boot/quotient/metadata.json').read_text()))
    cert=json.loads((root/'grammar-certificate.json').read_text());pm=json.loads(Path(parent).read_text())
    before,after=control_graph(pm),control_graph(cm)
    assert before==after==cert['reference_graph']==cert['candidate_graph']
    assert hashlib.sha256(json.dumps(before,separators=(',',':')).encode()).hexdigest()==cert['graph_sha256']
    return dict(checked_raw_rows=count,checked_primitive_occurrences=len(before),
                checked_control_edges=sum(len(x)-1 for x in before),selected_states=len(table(p/'boot/quotient/machine.tm'))//2)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--build',type=Path,required=True);p.add_argument('--parent',type=Path,required=True)
    p.add_argument('--vendor',type=Path,default=Path(__file__).resolve().parent/'baseline/code/shared/vendor/TMBuilder.py');a=p.parse_args()
    print(json.dumps(check(a.build,a.parent,a.vendor),indent=2))
