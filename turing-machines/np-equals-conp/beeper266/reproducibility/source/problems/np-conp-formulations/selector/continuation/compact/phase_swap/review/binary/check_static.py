"""Independent fresh allocation/storage/runtime/domain review of phase_swap.

The existing nonauthor row and abstract-state checkers are pinned, reused
dependencies. No producer compiler, selector solver or region module is loaded.
"""
from pathlib import Path
from copy import deepcopy
import argparse
import ast
import hashlib
import importlib.util
import json
import subprocess
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
COMPACT=ROOT.parent
PRIOR=COMPACT/'transfer328/review/binary'
PINS={
    'check_static.py':'40a6aabb3bfb7fab72c667962bcccc3c86415841cb858f9dcc71fa0003cf9e5f',
    'check_static291.py':'f09597a6fa5a5ca766152741421775274d2bd021bc1cf950ca6f4f1a8d8e0451',
}

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
for name,digest in PINS.items():assert sha(PRIOR/name)==digest,name
sys.path.insert(0,str(PRIOR))
spec=importlib.util.spec_from_file_location('independent_phase_swap_previous_static',PRIOR/'check_static291.py')
previous=importlib.util.module_from_spec(spec);spec.loader.exec_module(previous)
base=previous.base


def swaps(source,data):
    tree=ast.parse(source.read_text())
    main=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main')
    sites={}
    for node in ast.walk(main):
        if not (isinstance(node,ast.Assign) and len(node.targets)==1
                and isinstance(node.targets[0],ast.Tuple)
                and isinstance(node.value,ast.Tuple)):continue
        target=node.targets[0].elts;values=node.value.elts
        if not (len(target)==len(values)==2
                and all(isinstance(n,ast.Name) for n in target+values)):continue
        left,right=[n.id for n in target]
        if [n.id for n in values]!=[right,left]:continue
        assert left!=right
        sites[node.lineno]=(node,left,right)
    certificates=data['three-move-swap.json']
    assert len(sites)==len(certificates)==2
    assert {c['line'] for c in certificates}==set(sites)
    alloc=data['allocation.json']; mapping=alloc['mapping']
    frame=alloc['functions']['main']; physical=data['bank-coalescence.json']['mapping']
    retained=set(data['bank-projection.json']['retained_register_order'])
    result=[]
    for cert in certificates:
        node,left,right=sites[cert['line']]
        assert cert['function']=='main'
        assert cert['exact_ast']==ast.dump(node,include_attributes=False)
        assert [cert[k] for k in ('left','right','work')]==['main.'+left,'main.'+right,'$micro.q']
        assert right in frame['graph'][left] and left in frame['graph'][right]
        assert frame['colours'][left]!=frame['colours'][right]
        logical=[mapping[cert[k]] for k in ('left','right','work')]
        assert len(set(logical))==3
        # All three owners coexist during the closed swap. The actual lowerer
        # uses ordinary additive transfers; no atomic operand alias is licensed.
        assert set(logical)<=retained
        carriers=[physical[n] for n in logical]
        assert len(set(carriers))==3
        result.append(dict(line=node.lineno,logical=logical,physical=carriers))
    return dict(actual_source_swap_sites=result,
        scope='source tuple sites, declared operands and simultaneous distinct carriers; actual entry-zero premise and exact transfer refinement are separately reviewed; full intermediate ownership closure is checked below')


def run(parent,selected,plan,source):
    repo=next(p for p in HERE.parents if (p/'RESEARCH_PROTOCOL.md').is_file())
    old='problems/np-conp-formulations/selector/continuation/compact/transfer328/control/attempt_reset/source.py'
    producer='81147084e3d81219073ba6b8f0e6a3e3af8cf116'
    assert source.read_bytes()==subprocess.check_output(['git','-c','protocol.allow=never','show',producer+':'+old],cwd=repo)
    source_allocation=base.source_allocation
    def allocation(source,data):
        result=source_allocation(source,data)
        result['three_transfer_swap']=swaps(source,data)
        return result
    base.source_allocation=allocation
    try:result=previous.run(parent,selected,plan,source)
    finally:base.source_allocation=source_allocation
    pdata={p.name:base.load(p) for p in parent.glob('*.json')}
    bad=deepcopy(pdata);bad['three-move-swap.json'][0]['work']='main.left'
    try:swaps(source,bad)
    except AssertionError:pass
    else:raise AssertionError('aliased swap work certificate accepted')
    result['format']='np-conp-phase-swap-independent-static-v1'
    result['authorship']='nonauthor of selected source, swap region, clock, seed, consuming guards, completion and tables; author of separate unselected transfer328 action experiments'
    result['unchanged_source_binding']=dict(producer=producer,path=old,byte_equal=True)
    result['checker_sha256']=sha(__file__)
    result['prior_checker_pins']=PINS
    result['damaged_certificates_rejected'].append('aliased or wrong swap work certificate')
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('parent','selected','plan','source','out'):parser.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args()
    result=run(args.parent,args.selected,args.plan,args.source)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('artifacts','storage')},sort_keys=True,indent=2))
