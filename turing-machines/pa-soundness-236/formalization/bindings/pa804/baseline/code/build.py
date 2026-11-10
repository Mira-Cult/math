"""Minimal rebuilding closure for the hand-allocated compiler.

The generic source-language compiler is deliberately not reimplemented here.
These copied macro definitions and backend row formulas are exercised by the
exact 1062/926 table-hash controls. This is NOT a byte-identical build.py copy.
"""
from __future__ import annotations
import sys, json, hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE/'shared'),str(HERE/'shared/vendor')]
from TMBuilder import TMBuilder,subroutine,framework
from backend import totalize_silently
import tm

def dag_measures(builder):
    root=builder.find_seq('main().0'); done={}; active=set();todo=[(root,False)]
    while todo:
        node,leave=todo.pop()
        if not isinstance(node,int) or node in done: continue
        if not leave:
            if node in active: raise ValueError('cyclic source grammar')
            active.add(node);todo.append((node,True))
            todo.extend((c,False) for c in builder.sequences[node].seq)
        else:
            a,b=builder.sequences[node].seq
            ah,az=done[a] if isinstance(a,int) else (0,0)
            bh,bz=done[b] if isinstance(b,int) else (0,0)
            done[node]=(1+max(ah,bh),max(1+az,bz));active.remove(node)
    return root,done

class OmegaBuilder(TMBuilder):
    def __init__(self,source,*,share=False):
        super().__init__();self.source=source;self.share=share
        self.scratch=self.reg('scratch.copy')
    @subroutine
    def clear(self,x): return [self.while_decnz(x,())]
    @subroutine
    def move(self,out,x):
        assert out!=x
        return [self.while_decnz(x,out.inc)]
    @subroutine
    def copy(self,out,x):
        assert len({out,x,self.scratch})==3
        return [self.while_decnz(x,[out.inc,self.scratch.inc]),self.move(x,self.scratch)]
    @subroutine
    def dec(self,x): return [self.label('dec',[x.decnz,'break_dec'])]
    @subroutine
    def if_nz(self,x,body):
        if body==(): return []
        return [self.if_decnz(x,[x.inc,body])]
    @subroutine
    def if_zero(self,x,body):
        if body==(): return []
        return [self.label('zero',[[x.decnz,[x.inc,'break_zero']],body])]
    @subroutine
    def equal(self,out,a,b):
        return [self.label('eq',[
            self.while_decnz(a,[self.if_zero(b,[self.clear(a),'break_eq']),self.dec(b)]),
            self.if_zero(b,out.inc)]),self.clear(b)]
    def generate(self):
        root,measures=dag_measures(self);zero_depth=max(2+measures[root][1],2);rows=self.tm.states
        for lineno,line in enumerate(framework.splitlines()):self.tm.loadline(line,'<pinned-framework>',lineno)
        for i in range(1,zero_depth+1):
            rows[f'4.dispatch.{i}','0']=tm.Transition('0','L',f'4.dispatch.{i-1}')
            rows[f'4.dispatch.{i}','1']=tm.Transition('1','L',f'4.dispatch.{i}')
        rows['6.continue.0','1']=tm.Transition('1','L',f'4.dispatch.{zero_depth}')
        zero=next(r for r in self.registers.values() if rows[r.inc,'1'].nextstate=='2b.reg.0.inc')
        rows['0a.boot1.C','1']=tm.Transition('1','R',zero.inc)
        rows['0b.boot2.2','0']=tm.Transition('0','R',zero.inc)
        rows['0b.boot2.2','1']=tm.Transition('1','R',zero.decnz)
        def breaks(level):
            for k in range(1,level+1):
                rows[f'6.break.{k}','0']=tm.Transition('0','L',f'6.break.{k-1}')
                rows[f'6.break.{k}','1']=tm.Transition('0','L',f'6.break.{k}')
        def continues(level):
            for k in range(1,level+1):
                rows[f'6.continue.{k}','0']=tm.Transition('0','L',f'6.continue.{k}')
                rows[f'6.continue.{k}','1']=tm.Transition('0','L',f'6.continue.{k-1}')
        for node in self.reachable():
            sequence=self.sequences[node]
            for side,value in enumerate(sequence.seq):
                if isinstance(value,int):row=tm.Transition(str(side),'R',self.sequences[value].name)
                elif value.startswith('_break.'):
                    depth=int(value.split('.')[1])
                    if side==0 and depth==0:row=tm.Transition('1','L','6.continue.0')
                    else:
                        k=depth-1 if side==0 else depth;breaks(k)
                        row=tm.Transition('0','L',f'6.break.{k}')
                elif value.startswith('_continue.'):
                    k=int(value.split('.')[1])-side;assert k>=0;continues(k)
                    row=tm.Transition('0','L',f'6.continue.{k}')
                else:row=tm.Transition(str(side),'R',value)
                rows[sequence.name,str(side)]=row

def counted_initializer(builder):
    root,measures=dag_measures(builder);max_path=3+measures[root][0];anchor=max_path+3
    count=len(builder.registers);ones={0,1}|{anchor+2*i for i in range(count+1)}
    length=anchor+2*count+2;rows=builder.tm.states
    for i in range(length):
        write=str(int(i in ones));direction='R' if i+1<length else 'L'
        target=f'init.{i+1}' if i+1<length else 'init.scan'
        for read in '01':rows[f'init.{i}',read]=tm.Transition(write,direction,target)
    rows['init.scan','0']=tm.Transition('0','L','init.scan')
    rows['init.scan','1']=tm.Transition('1','L','init.previous')
    rows['init.previous','0']=tm.Transition('0','L','init.scan')
    rows['init.previous','1']=tm.Transition('1','R','init.right1')
    for read in '01':
        rows['init.right1',read]=tm.Transition(read,'R','init.right2')
        rows['init.right2',read]=tm.Transition(read,'R','main().0')
    builder.tm.start=builder.tm.statename='init.0'
    return dict(padding=anchor,registers=count,max_leaf_path=max_path,initializer_states=length+4,
                entry='main().0',head=3,ones=sorted(ones))

def number_rows(named,start='init.0'):
    states={q for q,_ in named};assert start in states
    order=[start]+sorted(states-{start});ids={q:i for i,q in enumerate(order)}
    return {(ids[q],b):(w,d,ids[t],e) for (q,b),(w,d,t,e) in named.items()},ids

def exact_quotient(rows):
    count=len(rows)//2;assert set(rows)=={(q,b) for q in range(count) for b in range(2)}
    colors=[0]*count;rounds=0
    while True:
        groups={};following=[]
        for q in range(count):
            signature=tuple((w,d,e,colors[t]) for w,d,t,e in (rows[q,0],rows[q,1]))
            if signature not in groups:groups[signature]=len(groups)
            following.append(groups[signature])
        rounds+=1
        if following==colors:break
        colors=following
    quotient={}
    for (q,b),(w,d,t,e) in rows.items():
        row=(w,d,colors[t],e);key=(colors[q],b)
        if key in quotient:assert quotient[key]==row
        quotient[key]=row
    assert colors[0]==0
    return quotient,dict(state_map=colors,refinement_rounds=rounds)

def table_text(rows):
    count=len(rows)//2
    lines=['#! format bit-events-v1',f'#! states {count}','#! start 0','#! blank 0','#! head 0']
    for q in range(count):
        for b in range(2):
            w,d,t,e=rows[q,b];lines.append(f'{q} {b} {w} {d} {t} {e}')
    return '\n'.join(lines)+'\n'

def write_machine(directory,rows,metadata):
    directory.mkdir(parents=True,exist_ok=True);text=table_text(rows)
    metadata=dict(metadata,states=len(rows)//2,transitions=len(rows),table_sha256=hashlib.sha256(text.encode()).hexdigest(),
                  table_bytes=len(text.encode()),event_rows={str(e):sum(row[3]==e for row in rows.values()) for e in ('0','1')})
    (directory/'machine.tm').write_text(text)
    (directory/'metadata.json').write_text(json.dumps(metadata,sort_keys=True,indent=2)+'\n')
    return metadata
