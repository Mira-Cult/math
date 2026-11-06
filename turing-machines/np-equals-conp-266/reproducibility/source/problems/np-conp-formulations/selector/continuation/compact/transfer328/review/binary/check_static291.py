"""Independent291 review, including its freshly derived dispatcher depth.

The302 checker remains unchanged.  This successor checks the one parameterized
runtime entry and every dispatcher row against actual grammar zero counts.
"""
from pathlib import Path
import argparse
import json
import subprocess
import check_static as base

HERE=Path(__file__).resolve().parent


def dispatcher(rows,depth):
    assert rows['6.continue.0',0]==(0,'L','6.continue.0',0)
    assert rows['6.continue.0',1]==(1,'L','4.dispatch.'+str(depth),0)
    for k in range(depth+1):
        name='4.dispatch.'+str(k)
        target='4.dispatch.'+str(k-1) if k else '4.dispatch.scan'
        assert rows[name,0]==(0,'L',target,0)
        assert rows[name,1]==(1,'L',name,0)
    assert rows['4.dispatch.scan',0]==(0,'R','4.dispatch.scan',0)
    assert rows['4.dispatch.scan',1]==(1,'R','5.root.1',0)


def runtime(parent,pdata):
    old=base.COMPACT/'phase_search/machines/normalized'
    repo=next(p for p in HERE.parents if (p/'RESEARCH_PROTOCOL.md').is_file())
    producer='f997ea51504460495a77fbb00c338a468db023b6'
    for name in ('raw.tm','names.json'):
        path=old/name
        assert subprocess.check_output(['git','-c','protocol.allow=never','show',producer+':'+path.relative_to(repo).as_posix()],cwd=repo)==path.read_bytes()
    def named(folder,names):
        reverse={q:n for n,q in names.items()};assert len(reverse)==len(names)
        return {(reverse[q],z):(w,d,reverse[t],e) for (q,z),(w,d,t,e) in base.completion.parse(folder/'raw.tm')[1].items()}
    oldnames=base.load(old/'names.json');names=pdata['names.json']
    oldrows=named(old,oldnames);rows=named(parent,names)
    paths=[row[0] for row in base.endpoint.Graph(pdata['grammar.json']).leaves]
    depth=max(path.count(0) for path in paths)+2
    assert pdata['selector.json']['old_dispatch_depth']==depth-1
    assert pdata['selector.json']['new_dispatch_depth']==depth
    actual={n for n in names if n.startswith('4.dispatch.') and n.rsplit('.',1)[1].isdigit()}
    assert actual=={'4.dispatch.'+str(i) for i in range(depth+1)}
    dispatcher(rows,depth)
    retained={n for n in names if not n.startswith(('compact_grammar_','main(','3.'))}
    assert retained<=set(oldnames)
    changed=[]
    for name in retained:
        for z in (0,1):
            expected=oldrows[name,z]
            if (name,z)==('6.continue.0',1):
                expected=(1,'L','4.dispatch.'+str(depth),0)
            assert rows[name,z]==expected,(name,z)
            if rows[name,z]!=oldrows[name,z]:changed.append(dict(state=name,read=z,before=list(oldrows[name,z]),after=list(rows[name,z])))
    assert len(changed)==1
    order=pdata['grammar.json']['registers'];native=pdata['native-runtime.json']['operands']
    assert order[:len(native)]==native
    entries=0
    for op in names:
        if not op.startswith('3.'):continue
        kind,register=base.endpoint.operand(op);entries+=2
        if kind=='half':
            assert rows[op,0]==(1,'R','2h.native_half.prep',0)
            assert rows[op,1]==(0,'R','2h.native_half.select.'+str(native.index(register)),0)
        else:
            assert kind in ('inc','decnz')
            assert rows[op,0]==(1,'R','1b.reg.prep_1',0)
            assert rows[op,1]==(int(kind=='decnz'),'R','shared.selector.select.'+str(order.index(register)+1),0)
    maximum=max(map(len,paths))
    assert maximum==pdata['selector.json']['max_leaf_path']<3822
    assert len(order)==pdata['selector.json']['registers']<=1909
    for name,digest in pdata['metadata.json']['producer_inputs'].items():assert base.sha(base.COMPACT/name)==digest,name
    bad=dict(rows);bad['6.continue.0',1]=(1,'L','4.dispatch.'+str(depth+1),0)
    try:dispatcher(bad,depth)
    except AssertionError:pass
    else:raise AssertionError('wrong dispatch entry accepted')
    return dict(frozen_runtime_producer=producer,literal_inherited_rows=2*len(retained)-len(changed),
        parameterized_runtime_rows=changed,checked_dispatch_rows=2*(depth+1)+4,
        derived_dispatch_depth=depth,depth_rule='max zero-count over complete unfolded 110-prefixed grammar paths, plus two',
        new_operation_entry_rows=entries,maximum_prepared_path=maximum,
        paid_bootstrap_zero_fields=1909,physical_classes=len(order),
        damaged_dispatch_target_rejected=True,
        domain_scope='same finite unary-bank/native-half/control-gap ABI; dispatcher depth freshly derived and its complete finite scan checked; all holes derived anew from raw fibers')


def run(parent,selected,plan,source):
    original=base.runtime;base.runtime=runtime
    try:result=base.run(parent,selected,plan,source)
    finally:base.runtime=original
    result['format']='np-conp-transfer291-independent-static-v1'
    result['checker_sha256']=base.sha(__file__)
    result['base_checker_sha256']=base.sha(Path(base.__file__))
    result['damaged_certificates_rejected'].append('incorrect parameterized dispatcher target')
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('parent','selected','plan','source','out'):p.add_argument('--'+name,type=Path,required=True)
    a=p.parse_args();result=run(a.parent,a.selected,a.plan,a.source)
    a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('artifacts','storage')},sort_keys=True,indent=2))
