"""Finite zero/one/many invariant and blank-run contextual quotient producer.

All discarded rows require the separately replayed abstract certificate. This is
not an all-configuration quotient. See CONTEXTUAL_QUOTIENT.md.
"""
from pathlib import Path
import sys, json, collections, hashlib
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'shared'))
from machine import Machine
from build_baseline import canonicalize, grammar
from quotient import quotient
if not __debug__: raise RuntimeError('certificate construction requires assertions enabled')


def machine_digest(machine):
    lines=['#! format beeper-v1',f'#! states {machine.count}',f'#! start {machine.start}',
           f'#! beep {machine.beep}','#! blank 0','#! head 0']
    for (q,b),(w,d,t) in sorted(machine.rows.items()):
        lines.append(f'{q} {b} {w} {"L" if d < 0 else "R"} {t}')
    return hashlib.sha256(('\n'.join(lines)+'\n').encode()).hexdigest()


def grammar_digest(builder):
    return hashlib.sha256(json.dumps(grammar(builder),sort_keys=True,separators=(',',':')).encode()).hexdigest()

def analyze(b):
 root=b.find_seq('main().0');nodes=tuple(tuple(s.seq) for s in b.sequences);regs=tuple(b.registers);idx={str(r):i for i,r in enumerate(regs)}
 occ=[]
 def walk(item,path,parent=None,bit=None):
  if isinstance(item,int):
   for bit,child in enumerate(nodes[item]):walk(child,path+str(bit),item,bit)
  else:occ.append((path,str(item),parent,bit))
 walk(root,'110');by_path={p:i for i,(p,*_) in enumerate(occ)}
 def resolve(path):
  if path.startswith('111'):path='110'
  if len(path)<3:path+='0'*(3-len(path))
  node=root;j=3
  while isinstance(node,int):
   if j==len(path):path+='0'
   node=nodes[node][int(path[j])];j+=1
  assert j==len(path),(path,node)
  return by_path[path]
 def ret(path,k):
  for j in range(len(path)-1,1,-1):
   if path[j]=='0':
    if k:k-=1
    else:return resolve(path[:j]+'1')
  raise ValueError(('bad return',path,k))
 def cont(path,k):
  for j in range(len(path)-1,0,-1):
   if path[j]=='1':
    if k:k-=1
    else:return resolve(path[:j+1])
  raise ValueError(('bad continue',path,k))
 edges=[]
 for p,op,parent,bit in occ:
  if op.startswith('_break.'):out=[(ret(p,int(op.split('.')[1])),None,None)]
  elif op.startswith('_continue.'):out=[(cont(p,int(op.split('.')[1])),None,None)]
  elif op=='beep':out=[(ret(p,0),None,None)]
  else:
   register,kind=op[2:].rsplit('.',1);v=idx[register]
   if kind=='inc':out=[(ret(p,0),v,'inc')]
   else:
    assert kind=='decnz';out=[(ret(p,0),v,'positive'),(ret(p,1),v,'zero')]
  edges.append(out)
 states=[None]*len(occ);start=resolve('110');states[start]=[1]*len(regs);q=collections.deque([start]);steps=0
 while q:
  i=q.popleft();state=states[i];steps+=1
  for j,v,op in edges[i]:
   out=state.copy()
   if op=='inc':out[v]=((2 if state[v]&1 else 0)|(4 if state[v]&6 else 0))
   elif op=='positive':
    if not state[v]&6:continue
    out[v]=(1 if state[v]&2 else 0)|(6 if state[v]&4 else 0)
   elif op=='zero':
    if not state[v]&1:continue
    out[v]=1
   prev=states[j]
   if prev is None:states[j]=out;q.append(j)
   else:
    merged=[a|c for a,c in zip(prev,out)]
    if merged!=prev:states[j]=merged;q.append(j)
 groups=collections.defaultdict(list);zero=[]
 for i,(p,op,parent,bit) in enumerate(occ):
  if states[i] is not None:
   groups[parent,bit].append(i)
   if op.endswith('.decnz') and states[i][idx[op[2:].rsplit('.',1)[0]]]==1:zero.append(i)
 replacements={k:'_break.1' for k,xs in groups.items() if all(i in zero for i in xs)}
 reachable_rows=set()
 for i,(p,op,*_) in enumerate(occ):
  if states[i] is not None:
   node=root
   for digit in p[3:]:
    reachable_rows.add((node,int(digit)));node=nodes[node][int(digit)]
 result=dict(occurrences=len(occ),reachable=sum(x is not None for x in states),zero_occurrences=len(zero),all_context_zero_groups=len(replacements),dead_grammar_rows=2*len(tuple(b.reachable()))-len(reachable_rows),iterations=steps)
 return result,replacements,reachable_rows,dict(occurrences=occ,states=states,edges=edges,root=root)



def apply(builder, raw=None, names=None):
    """Return (machine, certificate) without changing the caller's builder.

    The certificate checker performs no invariant or partition search. Runtime
    correctness and the exact blank initialization are separate caller premises.
    """
    expected_raw, expected_names = canonicalize(builder)
    if raw is None: raw = expected_raw
    if names is None: names = expected_names
    if (raw.start,raw.beep,raw.rows,names) != (expected_raw.start,expected_raw.beep,expected_raw.rows,expected_names):
        raise ValueError('raw table and names do not match the supplied builder')
    summary, replacements, live, abstract = analyze(builder)
    unknown = {(names[builder.sequences[i].name],bit)
               for i in builder.reachable() for bit in (0,1) if (i,bit) not in live}
    grammar_unknown = set(unknown)
    reachable = {raw.start}
    todo = [raw.start]
    while todo:
        q = todo.pop()
        for bit in (0,1):
            if (q,bit) in unknown: continue
            target = raw.rows[q,bit][2]
            if target not in reachable:
                reachable.add(target);todo.append(target)
    unknown.update((q,bit) for q in range(raw.count) if q not in reachable for bit in (0,1))

    class Partition:
        def __init__(self):
            self.parent=list(range(raw.count))
            self.rows=[[None if (q,b) in unknown else raw.rows[q,b] for b in (0,1)] for q in range(raw.count)]
            self.event=[q == raw.beep for q in range(raw.count)]
        def copy(self):
            other=object.__new__(Partition)
            other.parent=self.parent.copy()
            other.rows=[row.copy() for row in self.rows]
            other.event=self.event.copy()
            return other
        def find(self,q):
            while self.parent[q] != q: q=self.parent[q]
            return q
        def merge(self,a,b):
            pending=[(a,b)];merged=0
            while pending:
                a,b=(self.find(x) for x in pending.pop())
                if a == b: continue
                if self.event[a] != self.event[b]: return None
                if b < a: a,b=b,a
                for bit in (0,1):
                    left,right=self.rows[a][bit],self.rows[b][bit]
                    if left is not None and right is not None:
                        if left[:2] != right[:2]: return None
                        pending.append((left[2],right[2]))
                    elif right is not None: self.rows[a][bit]=right
                self.parent[b]=a;merged+=1
            return merged
        def roots(self): return [q for q in range(raw.count) if self.find(q) == q]

    partition=Partition()
    _, exact=quotient(raw)
    first={}
    for q in range(raw.count):
        if exact[q] in first:
            if partition.merge(q,first[exact[q]]) is None: raise AssertionError('exact quotient is incompatible')
        else: first[exact[q]]=q
    merges=[]
    while True:
        # Keep only the maximal trial, under exactly the original tie-break.
        # Retaining every copied partition uses cubic producer memory when a
        # fixed-input fixture makes many grammar rows unreachable. The selected
        # table/certificate and the independent no-search checker are unchanged.
        best=None;roots=partition.roots()
        for left in roots:
            if all(row is not None for row in partition.rows[left]): continue
            for right in roots:
                if left == right: continue
                trial=partition.copy();gain=trial.merge(left,right)
                if gain and (best is None or (gain,-left,-right) > (best[0],-best[1],-best[2])):
                    best=(gain,left,right,trial)
        if best is None: break
        gain,left,right,partition=best
        merges.append({'left':left,'right':right,'classes_removed':gain})
    roots=partition.roots()
    order=[partition.find(raw.start),partition.find(raw.beep)]
    order+=sorted(set(roots)-set(order))
    renumber={q:i for i,q in enumerate(order)}
    mapping={q:renumber[partition.find(q)] for q in range(raw.count)}
    rows={}
    for q in roots:
        for bit in (0,1):
            row=partition.rows[q][bit]
            if row is None: row=(bit,1,q)
            rows[renumber[q],bit]=(*row[:2],mapping[row[2]])
    selected, final_exact=quotient(Machine(mapping[raw.start],mapping[raw.beep],rows))
    mapping={q:final_exact[t] for q,t in mapping.items()}
    certificate={
        'schema':'horn-contextual-quotient-v1',
        'domain':'zero-register source entry reached by the separately checked blank bootstrap',
        'abstract_domain':{'1':'zero','2':'one','4':'at least two','union':'bitwise OR','unreachable':None},
        'grammar_sha256':grammar_digest(builder),
        'raw_table_sha256':machine_digest(raw),
        'table_sha256':machine_digest(selected),
        'states_at_occurrences':[None if state is None else ''.join(map(str,state)) for state in abstract['states']],
        'ignored_grammar_rows':[list(key) for key in sorted(grammar_unknown)],
        'ignored_rows':[list(key) for key in sorted(unknown)],
        'mapping':mapping,
        'measurements':{**summary,'raw_states':raw.count,'exact_states':len(set(exact.values())),
                        'selected_states':selected.count,'ignored_physical_rows':len(unknown)},
        'search_recipe':{'kind':'greedy compatible partial-row merges followed by exact quotient','merges':merges},
        'event_scope':'B colors and literal transition times preserved on the admitted blank run',
    }
    from check_contextual_quotient import check
    check(builder,raw,selected,names,certificate)
    return selected, certificate
