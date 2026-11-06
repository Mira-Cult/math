"""Independent selected-source allocation, storage, row/domain/event review.

The earlier independently written abstract and row checkers are explicit
dependencies.  No producer/compiler or completion solver is imported.
"""
from copy import deepcopy
from itertools import combinations
from pathlib import Path
import argparse
import ast
import hashlib
import importlib.util
import json
import subprocess

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
COMPACT=ROOT.parent


def load(path):return json.loads(Path(path).read_text())
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def jd(value):return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    result=importlib.util.module_from_spec(spec);spec.loader.exec_module(result);return result


PREVIOUS_COMPLETION=COMPACT/'binary_phase/review/phase_completion/check_completion.py'
PREVIOUS_ALLOCATION=COMPACT/'binary_phase/review/binary/check_static_parser.py'
PREVIOUS_STORAGE=COMPACT/'phase_search/review/certificate_engine/check_selected.py'
completion=module('transfer_independent_row_equations',PREVIOUS_COMPLETION)
allocation_checker=module('transfer_independent_source_cfg',PREVIOUS_ALLOCATION)
storage_checker=module('transfer_independent_abstract_storage',PREVIOUS_STORAGE)
endpoint=storage_checker.endpoint


def source_allocation(source,data):
    allocation=data['allocation.json']
    result=allocation_checker.source_cfg(source,allocation)
    tree=ast.parse(source.read_text())
    functions={n.name:n for n in tree.body if isinstance(n,ast.FunctionDef)}
    assert set(functions)=={'main'},'this review admits the explicit shared main frame'
    main=functions['main'];record=allocation['functions']['main']
    colour=record['colours'];interference=record['graph']
    clocks=[];guards=[];seeds=[]
    for node in ast.walk(main):
        for _,statements in ast.iter_fields(node):
            if not isinstance(statements,list) or not all(isinstance(n,ast.stmt) for n in statements):continue
            for index in range(len(statements)-2):
                first,second,third=statements[index:index+3]
                if not (isinstance(first,ast.Assign) and len(first.targets)==1 and isinstance(first.targets[0],ast.Name)
                        and isinstance(second,ast.Assign) and len(second.targets)==1 and isinstance(second.targets[0],ast.Name)
                        and isinstance(second.value,ast.Name)):continue
                F,S,K=first.targets[0].id,second.targets[0].id,second.value.id
                text=f'{F} = 1\n{S} = {K}\nwhile {S}:\n    {S} -= 1\n    {F} *= 2'
                if [ast.dump(n,include_attributes=False) for n in (first,second,third)] != [ast.dump(n,include_attributes=False) for n in ast.parse(text).body]:continue
                assert len({F,S,K})==3
                for a,b in combinations((F,S,K),2):
                    assert b in interference[a] and a in interference[b] and colour[a]!=colour[b]
                seeds.append(([first,second,third],[F,S,K]))
        if (isinstance(node,ast.Assign) and len(node.targets)==1
                and isinstance(node.targets[0],ast.Name) and isinstance(node.value,ast.BinOp)
                and isinstance(node.value.op,ast.Pow)):
            F=node.targets[0].id;expression=node.value
            assert isinstance(expression.right,ast.Name)
            assert isinstance(expression.left,ast.BinOp) and isinstance(expression.left.op,ast.Add)
            assert isinstance(expression.left.left,ast.Name)
            assert isinstance(expression.left.right,ast.Constant) and type(expression.left.right.value) is int and expression.left.right.value==1
            names=[F,expression.left.left.id,expression.right.id]
            assert len(set(names))==3
            for a,b in combinations(names,2):
                assert b in interference[a] and a in interference[b]
                assert colour[a]!=colour[b]
            clocks.append((node,names))
        if not (isinstance(node,ast.If) and isinstance(node.test,ast.Name) and node.body):continue
        first=node.body[0]
        if (isinstance(first,ast.AugAssign) and isinstance(first.target,ast.Name)
                and first.target.id==node.test.id and isinstance(first.op,ast.Sub)
                and isinstance(first.value,ast.Constant) and type(first.value.value) is int and first.value.value==1):
            guards.append(node)
    clockcert=data['direct-clock.json'];guardcert=data['consume-guard.json']
    assert len(clocks)==len(clockcert)==1
    assert len(guards)==len(guardcert)==3
    for (node,names),cert in zip(clocks,clockcert):
        assert cert['function']=='main' and cert['line']==node.lineno
        assert cert['exact_ast']==ast.dump(node,include_attributes=False)
        assert [cert[k] for k in ('output','length_master','exponent_master')]==['main.'+n for n in names]
        assert cert['borrow_exponent'] is True
        operands=[cert[k] for k in ('output','length_master','exponent_master','exponent_work','product_work','copy_scratch')]
        assert len(set(operands))==6
        for logical in operands:assert logical in allocation['mapping']
    expected={node.lineno:(node.test.id,ast.dump(node,include_attributes=False)) for node in guards}
    assert {cert['line'] for cert in guardcert}==set(expected)
    for cert in guardcert:
        name,encoded=expected[cert['line']]
        assert cert['function']=='main' and cert['operand']=='main.'+name and cert['exact_ast']==encoded
    seedcert=data['certificate-seed.json']
    assert len(seeds)==len(seedcert)==1
    for (nodes,names),cert in zip(seeds,seedcert):
        assert cert['function']=='main' and cert['line']==nodes[0].lineno
        assert cert['exact_ast']==[ast.dump(n,include_attributes=False) for n in nodes]
        assert [cert[k] for k in ('output','restore_counter','clock_master')]==['main.'+n for n in names]
        operands=[cert[k] for k in ('output','restore_counter','clock_master','double_work')]
        assert len(set(operands))==4 and all(n in allocation['mapping'] for n in operands)
    assert data['whole-action.json']==[]
    return dict(cfg=result,closed_clock_regions=len(clocks),consuming_guard_regions=len(guards),
        closed_seed_regions=len(seeds),clock_and_seed_three_operand_interference=True,
        scope='actual source CFG/liveness and extra simultaneous clock operands; closed region arithmetic and entry-zero premises reviewed separately')


def row_data(parent,selected,plan,source):
    data={}
    for key,path in [('raw',parent/'raw.tm'),('parent',parent/'machine.tm'),
                     ('completed',selected/'raw.tm'),('selected',selected/'machine.tm'),
                     ('ingress',selected/'ingress-prequotient.tm'),('marked',selected/'events.tm')]:
        _,data[key]=completion.parse(path)
    data['names']=load(parent/'names.json')
    data['first']=completion.map_list(load(parent/'quotient.json'),len(data['raw'])//2)
    data['second']=completion.map_list(load(selected/'quotient.json'),len(data['completed'])//2)
    data['event']=load(selected/'event-quotient.json')
    data['third']=completion.map_list(data['event']['mapping'],len(data['ingress'])//2)
    data['domain']=load(selected/'domain.json');data['plan']=load(plan)
    data['requested']=load(parent/'selector.json')['new_totalized_rows']
    for name,path in [('source_sha256',source),('control_sha256',parent/'machine.tm'),
                      ('source_request_file_sha256',parent/'selector.json'),('names_sha256',parent/'names.json'),
                      ('raw_quotient_sha256',parent/'quotient.json')]:
        assert data['domain'][name]==sha(path)
    assert data['plan']['source_sha256']==sha(source)
    assert data['plan']['control_sha256']==sha(parent/'machine.tm')
    for name,path in [('source_table_sha256',selected/'machine.tm'),('predecessor_sha256',selected/'ingress-prequotient.tm'),
                      ('result_sha256',selected/'events.tm')]:assert data['event'][name]==sha(path)
    return data


def runtime(parent,pdata):
    old=COMPACT/'phase_search/machines/normalized'
    repo=next(p for p in HERE.parents if (p/'RESEARCH_PROTOCOL.md').is_file())
    producer='f997ea51504460495a77fbb00c338a468db023b6'
    for name in ('raw.tm','names.json'):
        path=old/name
        assert subprocess.check_output(['git','-c','protocol.allow=never','show',producer+':'+path.relative_to(repo).as_posix()],cwd=repo)==path.read_bytes()
    def named(folder,names):
        reverse={q:n for n,q in names.items()};assert len(reverse)==len(names)
        return {(reverse[q],z):(w,d,reverse[t],e) for (q,z),(w,d,t,e) in completion.parse(folder/'raw.tm')[1].items()}
    oldnames=load(old/'names.json');names=pdata['names.json']
    oldrows=named(old,oldnames);rows=named(parent,names)
    retained={n for n in names if not n.startswith(('compact_grammar_','main(','3.'))}
    assert retained<=set(oldnames)
    for name in retained:
        for z in (0,1):assert rows[name,z]==oldrows[name,z],name
    order=pdata['grammar.json']['registers'];native=pdata['native-runtime.json']['operands']
    assert order[:len(native)]==native
    entries=0
    for op in names:
        if not op.startswith('3.'):continue
        kind,register=endpoint.operand(op);entries+=2
        if kind=='half':
            assert rows[op,0]==(1,'R','2h.native_half.prep',0)
            assert rows[op,1]==(0,'R','2h.native_half.select.'+str(native.index(register)),0)
        else:
            assert kind in ('inc','decnz')
            assert rows[op,0]==(1,'R','1b.reg.prep_1',0)
            assert rows[op,1]==(int(kind=='decnz'),'R','shared.selector.select.'+str(order.index(register)+1),0)
    paths=[row[0] for row in endpoint.Graph(pdata['grammar.json']).leaves]
    maximum=max(map(len,paths))
    assert maximum==pdata['selector.json']['max_leaf_path']<3822
    assert len(order)==pdata['selector.json']['registers']<=1909
    for name,digest in pdata['metadata.json']['producer_inputs'].items():assert sha(COMPACT/name)==digest,name
    return dict(frozen_runtime_producer=producer,literal_inherited_rows=2*len(retained),
        new_operation_entry_rows=entries,maximum_prepared_path=maximum,
        paid_bootstrap_zero_fields=1909,physical_classes=len(order),
        domain_scope='inherited finite unary-bank/native-half/control-gap ABI; all numerical exclusions derived anew from full raw fibers')


def damaged(parent,selected,plan,source,pdata,rdata):
    rejected=completion.mutations(rdata)
    def reject(label,call):
        try:call()
        except (AssertionError,KeyError,IndexError,ValueError):rejected.append(label);return
        raise AssertionError('damaged certificate accepted: '+label)
    bad=deepcopy(pdata);cert=bad['contextual-tree-certificate.json'];g=endpoint.Graph(cert['input_grammar'])
    value=list(cert['states_at_occurrences'][g.entry]);value[0]='2';cert['states_at_occurrences'][g.entry]=''.join(value)
    reject('false contextual entry',lambda:storage_checker.storage(bad))
    bad=deepcopy(pdata);sharing=bad['coalescence-invariant.json'];g=endpoint.Graph(sharing['input_grammar'])
    value=list(sharing['states_at_occurrences'][g.entry]);value[-1]='2';sharing['states_at_occurrences'][g.entry]=''.join(value)
    bad['bank-coalescence.json']['invariant_sha256']=jd(sharing)
    reject('false sharing entry with updated digest',lambda:storage_checker.storage(bad))
    bad=deepcopy(pdata);name=bad['bank-projection.json']['removed_registers'][0]
    bad['bank-projection.json']['removed_interpretation'][name]=1
    reject('nonzero projected-away coordinate',lambda:storage_checker.storage(bad))
    bad=deepcopy(pdata);colours=bad['allocation.json']['functions']['main']['colours'];colours['state']=colours['right']
    reject('live source state/right alias',lambda:source_allocation(source,bad))
    bad=deepcopy(pdata);cert=bad['direct-clock.json'][0];cert['borrow_exponent']=False
    reject('incorrect clock region mode',lambda:source_allocation(source,bad))
    bad=deepcopy(pdata);bad['consume-guard.json'][0]['operand']='main.branch'
    reject('wrong consuming guard operand',lambda:source_allocation(source,bad))
    bad=deepcopy(pdata);bad['certificate-seed.json'][0]['clock_master']='main.steps'
    reject('wrong borrowed seed clock',lambda:source_allocation(source,bad))
    return rejected


def run(parent,selected,plan,source):
    parent,selected,plan,source=map(Path,(parent,selected,plan,source))
    source_sha=sha(source)
    pdata={p.name:load(p) for p in parent.glob('*.json')}
    for folder in (parent,selected):
        meta=load(folder/'metadata.json');assert meta['source_sha256']==source_sha
        for key,name in [('raw_table_sha256','raw.tm'),('table_sha256','machine.tm'),('event_table_sha256','events.tm')]:assert meta[key]==sha(folder/name)
    storage_checker.SOURCE_SHA=source_sha
    rdata=row_data(parent,selected,plan,source)
    result=dict(format='np-conp-transfer-independent-static-v1',reviewer='internal-model-reviewer',
        authorship='nonauthor of selected source, clock, consuming guards, completion and tables; author of separate unselected action experiments',
        source_sha256=source_sha,checker_sha256=sha(__file__),
        reused_checkers={p.relative_to(COMPACT).as_posix():sha(p) for p in (PREVIOUS_COMPLETION,PREVIOUS_ALLOCATION,PREVIOUS_STORAGE)},
        source_allocation=source_allocation(source,pdata),storage=storage_checker.storage(pdata),
        runtime=runtime(parent,pdata),completion=completion.check(rdata),
        damaged_certificates_rejected=damaged(parent,selected,plan,source,pdata,rdata),
        plan_sha256=sha(plan),
        artifacts={name:{p.name:sha(p) for p in sorted(folder.iterdir()) if p.is_file()} for name,folder in [('parent',parent),('selected',selected)]},
        scope='independent conventional domain review and all-row/full-fiber/storage/allocation checks; source theorem, literal replay and immutable-object binding have separately recorded scopes')
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('parent','selected','plan','source','out'):p.add_argument('--'+name,type=Path,required=True)
    a=p.parse_args();result=run(a.parent,a.selected,a.plan,a.source)
    a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('artifacts','storage')},sort_keys=True,indent=2))
