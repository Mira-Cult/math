"""Nonauthor literal completion review, independent of producer row helpers.

New code parses tables, derives complete fibers and checks every row equation.
It explicitly reuses the earlier independently written abstract storage checker
for the unchanged single-operand native runtime contracts. No producer module,
completion solver or coordinator checker is imported.
"""
import argparse
import ast
from collections import defaultdict
from copy import deepcopy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
COMPACT=ROOT.parent
SOURCE=ROOT/'control/source_direct_branches.py'
SOURCE_SHA='3209d74668903ca99a3dcd60343be3b9ddde61ee9b2b226019eb1d3bcc9f4840'
SOURCES={'branches':(SOURCE,SOURCE_SHA),
         'parser':(ROOT/'control/parser/source.py','46f2a7273f0dfeca71c851f02b5e364836f62fad4eef622ea6a8ee48e6515de5')}
EXCLUDED={
    '1b.reg.prep_1':1,
    '2h.native_half.begin':0,
    '2h.native_half.boundary':1,
    '2h.native_half.prep':1,
    '2h.native_half.undo':0,
    'shared.selector.bootstrap.prep':1,
    'shared.selector.mark':0,
    'shared.selector.mode0.pad1':1,
    'shared.selector.mode0.pad2':1,
    'shared.selector.mode1.pad1':1,
    'shared.selector.mode1.pad2':1,
    'shared.selector.prep':1,
    'shared.selector.skip_separator':1,
}


def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def load(path):return json.loads(Path(path).read_text())


def parse(path):
    header={};rows={}
    for line in Path(path).read_text().splitlines():
        if line.startswith('#! '):
            key,value=line[3:].split(' ',1);assert key not in header;header[key]=value
        elif line.strip():
            fields=line.split();assert len(fields) in (5,6)
            q,z,w=int(fields[0]),int(fields[1]),int(fields[2]);d=fields[3];t=int(fields[4]);e=int(fields[5]) if len(fields)==6 else 0
            assert z in (0,1) and w in (0,1) and d in ('L','R') and e in (0,1)
            assert (q,z) not in rows;rows[q,z]=(w,d,t,e)
    n=int(header['states'])
    assert header['format'] in ('beeper-v1','beeper-events-v1')
    if header['format']=='beeper-v1':assert header['beep']=='1'
    assert header['start']==header['blank']==header['head']=='0'
    assert set(rows)=={(q,z) for q in range(n) for z in (0,1)}
    assert all(0<=v[2]<n for v in rows.values())
    return header,rows


def map_list(value,n):
    if isinstance(value,list):assert len(value)==n;return list(value)
    assert set(value)=={str(i) for i in range(n)}
    return [value[str(i)] for i in range(n)]


def equation(before,after,mapping):
    assert len(mapping)*2==len(before)
    assert set(mapping)==set(range(len(after)//2)) and mapping[0]==0
    for (q,z),(w,d,t,e) in before.items():
        assert after[mapping[q],z]==(w,d,mapping[t],e)


def check(data):
    raw=data['raw'];parent=data['parent'];names=data['names'];first=data['first']
    completed=data['completed'];selected=data['selected'];second=data['second']
    ingress=data['ingress'];marked=data['marked'];third=data['third'];domain=data['domain']
    assert set(names.values())==set(range(len(raw)//2)) and len(set(names.values()))==len(names)
    assert {(name,int(z)) for name,z in data['requested']}==set(EXCLUDED.items())
    blocked={(names[n],z) for n,z in EXCLUDED.items()}|{(names['silent.sink'],z) for z in (0,1)}
    assert {(q,z) for (q,z),v in raw.items() if v[2]==names['silent.sink']}==blocked
    equation(raw,parent,first)
    assert first[1]==1 and [q for q,c in enumerate(first) if c==1]==[1]
    fibers=defaultdict(list)
    for q,c in enumerate(first):fibers[c].append(q)
    holes={(q,z) for q,olds in fibers.items() for z in (0,1) if all((old,z) in blocked for old in olds)}
    assert holes==set(map(tuple,domain['holes']))==set(map(tuple,data['plan']['holes']))
    assert domain['preimages']=={str(q):fibers[q] for q,z in sorted(holes)}
    assert domain['sink']==first[names['silent.sink']]
    assert all(parent[k][2]==domain['sink'] for k in holes)
    assert set(completed)==set(parent)
    assert all(completed[k]==parent[k] for k in parent if k not in holes)
    assert second==data['plan']['mapping']
    assert second[1]==1 and [q for q,c in enumerate(second) if c==1]==[1]
    equation(completed,selected,second)
    assert len(ingress)==len(selected)
    for key,(w,d,t,old_event) in selected.items():
        assert old_event==0
        assert ingress[key]==(w,d,t,int(t==1))
    assert all(selected[1,z][2]!=1 for z in (0,1))
    equation(ingress,marked,third)
    assert data['event']['source_B']==1 and data['event']['time_shift']==-1
    return {'raw_rows':len(raw),'named_exclusions':len(EXCLUDED),
            'projected_holes':[list(k) for k in sorted(holes)],
            'retained_parent_rows':len(parent)-len(holes),
            'actual_completed_row_changes':sum(parent[k]!=completed[k] for k in holes),
            'completion_equations':len(completed),'event_equations':len(ingress),
            'raw_states':len(raw)//2,'parent_states':len(parent)//2,
            'B_states':len(selected)//2,'marked_states':len(marked)//2,
            'marked_rows':[[q,z,*v] for (q,z),v in sorted(marked.items()) if v[3]]}


def mutations(data):
    rejected=[]
    def reject(label,mutate):
        bad=deepcopy(data);mutate(bad)
        try:check(bad)
        except (AssertionError,KeyError,IndexError,ValueError):rejected.append(label);return
        raise AssertionError('damaged input accepted: '+label)
    reject('remove raw preimage',lambda d:d['domain']['preimages'].__setitem__(str(d['domain']['holes'][0][0]),[]))
    reject('add unconstrained row',lambda d:d['domain']['holes'].append([0,0]))
    reject('remove named semantic exclusion',lambda d:d['requested'].pop())
    reject('merge B into start',lambda d:d['second'].__setitem__(1,0))
    reject('erase event shift',lambda d:d['event'].__setitem__('time_shift',0))
    for field,label in enumerate(('write','move','target','event')):
        def change(d):
            value=list(d['selected'][0,0]);value[field]=[1-value[0],'L' if value[1]=='R' else 'R',(value[2]+1)%(len(d['selected'])//2),1-value[3]][field]
            d['selected'][0,0]=tuple(value)
        reject('damage selected '+label,change)
    reject('erase ingress event',lambda d:d['ingress'].__setitem__(next(k for k,v in d['ingress'].items() if v[3]),(0,'R',0,0)))
    reject('change retained completion row',lambda d:d['completed'].__setitem__((0,0),(0,'R',0,0)))
    return rejected


def run(parent,selected,planfile,case='branches'):
    source,source_sha=SOURCES[case]
    assert sha(source)==source_sha
    for folder in (parent,selected):
        metadata=load(folder/'metadata.json')
        assert metadata['source_sha256']==source_sha
        for key,name in [('raw_table_sha256','raw.tm'),('table_sha256','machine.tm'),('event_table_sha256','events.tm')]:
            assert metadata[key]==sha(folder/name)
    data={}
    for key,path in [('raw',parent/'raw.tm'),('parent',parent/'machine.tm'),
                     ('completed',selected/'raw.tm'),('selected',selected/'machine.tm'),
                     ('ingress',selected/'ingress-prequotient.tm'),('marked',selected/'events.tm')]:
        header,data[key]=parse(path)
    data['names']=load(parent/'names.json')
    data['first']=map_list(load(parent/'quotient.json'),len(data['raw'])//2)
    data['second']=map_list(load(selected/'quotient.json'),len(data['completed'])//2)
    data['event']=load(selected/'event-quotient.json')
    data['third']=map_list(data['event']['mapping'],len(data['ingress'])//2)
    data['domain']=load(selected/'domain.json');data['plan']=load(planfile)
    data['requested']=load(parent/'selector.json')['new_totalized_rows']
    for name,path in [('source_sha256',source),('control_sha256',parent/'machine.tm'),
                      ('source_request_file_sha256',parent/'selector.json'),('names_sha256',parent/'names.json'),
                      ('raw_quotient_sha256',parent/'quotient.json')]:
        assert data['domain'][name]==sha(path)
    assert data['plan']['source_sha256']==source_sha
    assert data['plan']['control_sha256']==sha(parent/'machine.tm')
    for name,path in [('source_table_sha256',selected/'machine.tm'),('predecessor_sha256',selected/'ingress-prequotient.tm'),
                      ('result_sha256',selected/'events.tm')]:assert data['event'][name]==sha(path)
    # The candidate enumeration and comparison suffix remain AST equivalent.
    # In the parser case only normalization statements are changed; their
    # value adapter is the separately reviewed parser source obligation.
    old_source=COMPACT/'phase_search/coordinator/pair_normalize.py'
    def function(path,name):return next(n for n in ast.parse(path.read_text()).body if isinstance(n,ast.FunctionDef) and n.name==name)
    if case=='branches':
        assert ast.dump(function(old_source,'main'),include_attributes=False)==ast.dump(function(source,'main'),include_attributes=False)
    else:
        assert ast.dump(function(SOURCE,'accept'),include_attributes=False)==ast.dump(function(source,'accept'),include_attributes=False)
        def skeleton(path):
            tree=function(path,'main');inner=tree.body[1].body[2]
            assert isinstance(inner,ast.While) and isinstance(inner.body[-2],ast.If) and isinstance(inner.body[-1],ast.AugAssign)
            inner.body=inner.body[-2:]
            return ast.dump(tree,include_attributes=False)
        assert skeleton(old_source)==skeleton(source)
    # Compare all named non-grammar runtime rows against the actual frozen
    # producer's Git objects before using its semantic domain contracts.
    repo=next(p for p in HERE.parents if (p/'RESEARCH_PROTOCOL.md').is_file())
    old=COMPACT/'phase_search/machines/normalized';producer='f997ea51504460495a77fbb00c338a468db023b6'
    for file in ('raw.tm','names.json'):
        p=old/file
        assert subprocess.check_output(['git','-c','protocol.allow=never','show',producer+':'+p.relative_to(repo).as_posix()],cwd=repo)==p.read_bytes()
    def named(rows,names):
        reverse={q:n for n,q in names.items()}
        return {(reverse[q],z):(w,d,reverse[t],e) for (q,z),(w,d,t,e) in rows.items()}
    oldnamed=named(parse(old/'raw.tm')[1],load(old/'names.json'))
    newnamed=named(data['raw'],data['names'])
    retained={n for n in data['names'] if not n.startswith(('compact_grammar_','main(','3.'))}
    for n in retained:
        for z in (0,1):assert newnamed[n,z]==oldnamed[n,z]
    # Reused independent abstract-transfer checker; fresh certificates only.
    earlier=COMPACT/'phase_search/review/certificate_engine/check_selected.py'
    spec=importlib.util.spec_from_file_location('phase_completion_independent_storage',earlier)
    checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
    checker.SOURCE_SHA=source_sha
    parent_data={p.name:load(p) for p in parent.glob('*.json')}
    storage=checker.storage(parent_data)
    order=parent_data['grammar.json']['registers'];native=parent_data['native-runtime.json']['operands']
    assert order[:len(native)]==native
    entry_rows=0
    for n in data['names']:
        if not n.startswith('3.'):continue
        entry_rows+=2
        if n.startswith('3.$native-half:'):
            operand,suffix=n.split(':',1)[1].rsplit('.',1)
            assert suffix=='decnz'
            assert newnamed[n,0]==(1,'R','2h.native_half.prep',0)
            assert newnamed[n,1]==(0,'R','2h.native_half.select.'+str(native.index(operand)),0)
        else:
            kind,operand=checker.endpoint.operand(n)
            assert kind in ('inc','decnz')
            assert newnamed[n,0]==(1,'R','1b.reg.prep_1',0)
            assert newnamed[n,1]==(int(kind=='decnz'),'R','shared.selector.select.'+str(order.index(operand)+1),0)
    maximum=max(len(path) for path,*_ in checker.endpoint.Graph(parent_data['grammar.json']).leaves)
    assert maximum==parent_data['selector.json']['max_leaf_path']<3822
    assert len(order)==parent_data['selector.json']['registers']<=1909
    result=check(data)
    result.update(format='np-conp-independent-phase-completion-review-v1',
        reviewer='internal-model-reviewer',authorship='nonauthor of selected source, lowerings, completion wrapper and complete tables; author of unrelated native phase probes',
        source_sha256=source_sha,case=case,checker_sha256=sha(Path(__file__)),reused_storage_checker_sha256=sha(earlier),
        exact_frozen_runtime_rows=2*len(retained),checked_operation_entry_rows=entry_rows,
        maximum_prepared_path=maximum,paid_initial_zero_fields=1909,storage=storage,
        damaged_certificates_rejected=mutations(data),
        plan_sha256=sha(planfile),artifacts={label:{p.name:sha(p) for p in sorted(folder.iterdir()) if p.is_file()} for label,folder in [('parent',parent),('selected',selected)]},
        scope='Conventional semantic-domain review plus fresh full-preimage and all-row equations. Finite blank replay, source-CFG allocation review and exact Git freeze binding are separate.')
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--parent',type=Path,required=True)
    p.add_argument('--selected',type=Path,required=True);p.add_argument('--plan',type=Path,required=True);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--case',choices=sorted(SOURCES),default='branches')
    args=p.parse_args();result=run(args.parent,args.selected,args.plan,args.case)
    args.out.parent.mkdir(parents=True,exist_ok=True);args.out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('artifacts','storage')},sort_keys=True,indent=2))
