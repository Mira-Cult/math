"""Fresh actual clock/seed/swap entry review on the changed source.

Reuses the predecessor's nonauthor tuple/region checker, never the producer's
extractor. No old receipt, source-identity assertion or acceptance is reused.
"""
from copy import deepcopy
from itertools import product
from pathlib import Path
import argparse
import ast
import hashlib
import importlib.util
import json

HERE=Path(__file__).resolve().parent
COMPACT=HERE.parents[2]
CLOSED=COMPACT/'transfer328/review/source/check_closed_regions.py'
SWAP=COMPACT/'phase_swap/review/source/check_swap.py'


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    result=importlib.util.module_from_spec(spec);spec.loader.exec_module(result);return result


closed=module('control_review_previous_closed',CLOSED)
swaps=module('control_review_previous_swap',SWAP)


def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def arithmetic_regions(parent):
    """The selected zero pass may remove an actually zero clock output clear."""
    read=lambda name:json.loads((parent/name).read_text())
    grammar=read('pre-coalescence-grammar.json');graph=closed.TupleGraph(grammar)
    allocation=read('allocation.json')['mapping'];sharing=read('bank-coalescence.json')['mapping']
    invariant=read('coalescence-invariant.json');summary=closed.check_closure(graph,invariant,sharing)
    actual=lambda name:allocation.get(name,name)
    op=lambda name,kind:'3.'+name+'.'+kind
    clock,=read('direct-clock.json');seed,=read('certificate-seed.json')
    F,N,K,B,Q,C=[actual(clock[k]) for k in ('output','length_master','exponent_master','exponent_work','product_work','copy_scratch')]
    assert len({F,N,K,B,Q,C})==len({sharing[x] for x in (F,N,K,B,Q,C)})==6
    pattern=[(op(F,'decnz'),0,1),(op(F,'inc'),2),(op(K,'decnz'),3,13),(op(B,'inc'),4),
        (op(F,'decnz'),5,11),(op(N,'decnz'),6,8),(op(Q,'inc'),7),(op(C,'inc'),5),
        (op(C,'decnz'),9,10),(op(N,'inc'),8),(op(Q,'inc'),4),(op(Q,'decnz'),12,2),
        (op(F,'inc'),11),(op(B,'decnz'),14,15),(op(K,'inc'),13)]
    omitted_clear=False
    try:mapping,incoming,outgoing=closed.locate(graph.rows,pattern)
    except AssertionError:
        # This is a different admitted contract, never a relaxation of locate.
        pattern=[(row[0],*[i-1 for i in row[1:]]) for row in pattern[1:]]
        mapping,incoming,outgoing=closed.locate(graph.rows,pattern);omitted_clear=True
    def zero(entry,names):
        word=invariant['states_at_occurrences'][graph.indices[entry]]
        assert word is not None
        return all(word[grammar['registers'].index(name)]=='1' for name in names)
    required=(F,B,Q,C) if omitted_clear else (B,Q,C)
    assert zero(mapping[0],required),'clock zero premise is absent at its actual entry'
    stale_values=(0,) if omitted_clear else (0,3,19)
    cases=[(n,k,stale) for n in range(5) for k in range(5) for stale in stale_values]
    cases += [(2**100+7,0,0),(0,257,0),(1,9,0)]
    total=0
    for n,k,stale in cases:
        before={name:100+i for i,name in enumerate(grammar['registers'])}
        before.update({F:stale,N:n,K:k,B:0,Q:0,C:0})
        after,steps=closed.execute(graph.rows,mapping[0],mapping[len(pattern)],before)
        assert after==dict(before,**{F:(n+1)**k}) and steps>0;total+=steps
    clock_result=dict(rows=len(pattern),entry=''.join(map(str,mapping[0])),output_clear_removed=omitted_clear,
        entry_zero_carriers=list(required),logical_carriers=[F,N,K,B,Q,C],physical_carriers=[sharing[x] for x in (F,N,K,B,Q,C)],
        outside_entries=len(incoming),outside_exits=len(outgoing),fixtures=len(cases),primitive_steps=total)
    if omitted_clear:
        before={name:0 for name in grammar['registers']};before.update({F:1,N:2,K:0})
        after,_=closed.execute(graph.rows,mapping[0],mapping[len(pattern)],before)
        assert after[F]==2 and after[F]!=(before[N]+1)**before[K]
        clock_result['necessary_zero_counterexample']=dict(output_initial=1,length_initial=2,exponent_initial=0,actual_output=2,required_output=1)
    damaged=deepcopy(graph.rows)
    restore=len(pattern)-1
    damaged[mapping[restore]]=(op(F,'inc'),mapping[restore-1])
    try:closed.locate(damaged,pattern)
    except AssertionError:pass
    else:raise AssertionError('wrong exponent restoration accepted')

    # The old value of source n dies at e=n. The actual lowering drains it
    # through the ordinary assignment temporary, clears stale e, and moves
    # the temporary to e. This explains F=0 without a source-name shortcut.
    clock_entry=mapping[0];clock_exit=mapping[len(pattern)]
    T=actual('$pool0.tmp0')
    assert len({F,N,T})==len({sharing[x] for x in (F,N,T)})==3
    copy_pattern=[(op(F,'decnz'),1,2),(op(T,'inc'),0),(op(N,'decnz'),2,3),
                  (op(T,'decnz'),4,5),(op(N,'inc'),3)]
    copied,copy_in,copy_out=closed.locate(graph.rows,copy_pattern)
    assert copied[5]==clock_entry
    copy_images=[swaps.edge_work_image(graph,invariant,a,b,T) for a,b in copy_in]
    assert any(copy_images) and all(x in (0,1) for x in copy_images),'assignment temporary not zero on an outside entry'
    copy_steps=0
    copy_cases=list(product((0,1,2,7,31,127),(0,1,2,7,31,255)))
    for old_n,old_e in copy_cases:
        before={name:300+i for i,name in enumerate(grammar['registers'])}
        before.update({F:old_n,N:old_e,T:0})
        after,steps=closed.execute(graph.rows,copied[0],copied[5],before)
        assert after==dict(before,**{F:0,N:old_n,T:0})
        assert steps==4*old_n+old_e+3>0;copy_steps+=steps
    role_copy=dict(entry=''.join(map(str,copied[0])),rows=5,
        logical_carriers=[F,N,T],physical_carriers=[sharing[x] for x in (F,N,T)],
        outside_entry_temporary_images=copy_images,outside_entries=len(copy_in),outside_exits=len(copy_out),
        joined_loop_temporary_mask=invariant['states_at_occurrences'][graph.indices[copied[0]]][grammar['registers'].index(T)],
        exit_is_clock_entry=True,fixtures=len(copy_cases),primitive_steps=copy_steps,
        relation='(old_n,old_e,T=0) -> (0,old_n,0); old source n is dead until overwritten by the clock')

    F,S,K,Q=[actual(seed[k]) for k in ('output','restore_counter','clock_master','double_work')]
    assert len({F,S,K,Q})==len({sharing[x] for x in (F,S,K,Q)})==4
    pattern=[(op(F,'decnz'),0,1),(op(F,'inc'),2),(op(K,'decnz'),3,9),(op(S,'inc'),4),
        (op(F,'decnz'),5,7),(op(Q,'inc'),6),(op(Q,'inc'),4),(op(Q,'decnz'),8,2),
        (op(F,'inc'),7),(op(S,'decnz'),10,11),(op(K,'inc'),9)]
    mapping,incoming,outgoing=closed.locate(graph.rows,pattern)
    assert zero(mapping[0],(S,Q)),'certificate work not zero at its actual entry'
    total=0
    for clock_value in range(11):
        for stale in (0,3,19):
            before={name:200+i for i,name in enumerate(grammar['registers'])}
            before.update({F:stale,S:0,K:clock_value,Q:0})
            after,steps=closed.execute(graph.rows,mapping[0],mapping[len(pattern)],before)
            assert after==dict(before,**{F:1<<clock_value}) and steps>0;total+=steps
    seed_result=dict(rows=len(pattern),entry=''.join(map(str,mapping[0])),entry_zero_carriers=[S,Q],
        logical_carriers=[F,S,K,Q],physical_carriers=[sharing[x] for x in (F,S,K,Q)],
        outside_entries=len(incoming),outside_exits=len(outgoing),fixtures=33,primitive_steps=total)
    damaged=deepcopy(graph.rows);damaged[mapping[6]]=(op(S,'inc'),mapping[4])
    try:closed.locate(damaged,pattern)
    except AssertionError:pass
    else:raise AssertionError('wrong seed doubling accepted')
    seed_entry=mapping[0]

    # The second new carrier assignment must preserve j for subsequent input
    # stages and candidate enumeration. Inspect its whole restoring copy.
    E=allocation['main.e'];J=allocation['main.j'];T=actual('$pool0.tmp0');C=actual('$scratch.copy')
    assert len({E,J,T,C})==len({sharing[x] for x in (E,J,T,C)})==4
    copy_pattern=[(op(J,'decnz'),1,3),(op(T,'inc'),2),(op(C,'inc'),0),
        (op(C,'decnz'),4,5),(op(J,'inc'),3),(op(E,'decnz'),5,6),
        (op(T,'decnz'),7,8),(op(E,'inc'),6)]
    copied,copy_in,copy_out=closed.locate(graph.rows,copy_pattern)
    assert copied[0]==clock_exit and copied[8]==seed_entry
    entry_images={name:[swaps.edge_work_image(graph,invariant,a,b,name) for a,b in copy_in] for name in (T,C)}
    assert all(any(values) and all(x in (0,1) for x in values) for values in entry_images.values())
    copy_steps=0
    for exponent,stale in copy_cases:
        before={name:400+i for i,name in enumerate(grammar['registers'])}
        before.update({J:exponent,E:stale,T:0,C:0})
        after,steps=closed.execute(graph.rows,copied[0],copied[8],before)
        assert after==dict(before,**{E:exponent}) and steps==7*exponent+stale+4>0
        copy_steps+=steps
    description_copy=dict(rows=8,entry=''.join(map(str,copied[0])),entry_is_clock_exit=True,exit_is_seed_entry=True,
        logical_carriers=[E,J,T,C],physical_carriers=[sharing[x] for x in (E,J,T,C)],
        outside_entry_scratch_images=entry_images,outside_entries=len(copy_in),outside_exits=len(copy_out),
        fixtures=len(copy_cases),primitive_steps=copy_steps,relation='e<-j while j, clock and every other logical value are preserved; T=C=0 restored')
    damaged=deepcopy(graph.rows);damaged[copied[4]]=(op(E,'inc'),copied[3])
    try:closed.locate(damaged,copy_pattern)
    except AssertionError:pass
    else:raise AssertionError('candidate-index restoration damage accepted')
    return dict(**summary,clock=clock_result,role_copy=role_copy,description_copy=description_copy,certificate_seed=seed_result,
        mutations_rejected=['clock exponent restoration','certificate doubling','candidate index restoration'])


def run(parent,source):
    parent,source=Path(parent),Path(source)
    read=lambda name:json.loads((parent/name).read_text())
    tree=ast.parse(source.read_text())
    allocation=read('allocation.json')['mapping']
    naming=lambda x:allocation.get(x,x)
    powers=[node for node in ast.walk(tree) if isinstance(node,ast.Assign) and isinstance(node.value,ast.BinOp) and isinstance(node.value.op,ast.Pow)]
    assert len(powers)==1 and ast.dump(powers[0],include_attributes=False)==ast.dump(ast.parse('n = (e + 1) ** j').body[0],include_attributes=False)
    clock,=read('direct-clock.json')
    assert (clock['line'],clock['exact_ast'])==(powers[0].lineno,ast.dump(powers[0],include_attributes=False))
    assert [naming(clock[k]) for k in ('output','length_master','exponent_master')]==[allocation['main.'+v] for v in ('n','e','j')]
    inherited=arithmetic_regions(parent)

    grammar=read('pre-coalescence-grammar.json');graph=closed.TupleGraph(grammar)
    invariant=read('coalescence-invariant.json');sharing=read('bank-coalescence.json')['mapping']
    certificates=read('three-move-swap.json')
    assignment=ast.dump(ast.parse('left, right = right, left').body[0],include_attributes=False)
    actual=[n for n in ast.walk(tree) if isinstance(n,ast.Assign) and ast.dump(n,include_attributes=False)==assignment]
    assert len(actual)==len(certificates)==2
    assert sorted((n.lineno,ast.dump(n,include_attributes=False)) for n in actual)==sorted((c['line'],c['exact_ast']) for c in certificates)
    roles=[]
    for cert in certificates:
        assert cert['function']=='main'
        assert [cert[k] for k in ('left','right','work')]==['main.left','main.right','$micro.q']
        roles.append(tuple(naming(cert[k]) for k in ('left','right','work')))
    assert roles[0]==roles[1]
    L,R,Q=roles[0]
    op=lambda name,kind:'3.'+name+'.'+kind
    pattern=[(op(L,'decnz'),1,2),(op(Q,'inc'),0),(op(R,'decnz'),3,4),
             (op(L,'inc'),2),(op(Q,'decnz'),5,6),(op(R,'inc'),4)]
    turn=allocation['main.state']
    matches=swaps.region_premises(graph,invariant,sharing,roles[0],pattern,turn)
    fixtures=list(product((0,1,2,3,7,31,127,255),repeat=2))+[(1024,2047),(4096,0),(0,4096)]
    checked=[];total=0
    for mapping,incoming,outgoing in matches:
        subtotal=0
        for left,right in fixtures:
            initial={name:100+i for i,name in enumerate(grammar['registers'])}
            initial.update({L:left,R:right,Q:0})
            first,n1=closed.execute(graph.rows,mapping[0],mapping[2],initial)
            assert first==dict(initial,**{L:0,R:right,Q:left})
            second,n2=closed.execute(graph.rows,mapping[2],mapping[4],first)
            assert second==dict(initial,**{L:right,R:0,Q:left})
            final,n3=closed.execute(graph.rows,mapping[4],mapping[6],second)
            assert final==dict(initial,**{L:right,R:left,Q:0})
            assert n1+n2+n3==4*left+2*right+3>0
            subtotal+=n1+n2+n3
        total+=subtotal
        checked.append(dict(entry=''.join(map(str,mapping[0])),outside_entries=len(incoming),outside_exits=len(outgoing),
            entry_zero_images=[swaps.edge_work_image(graph,invariant,a,b,Q) for a,b in incoming],
            logical_carriers=[L,R,Q],physical_carriers=[sharing[x] for x in (L,R,Q)],
            fixtures=len(fixtures),primitive_steps=subtotal))
    mapping,incoming,_=matches[0]
    bad_graph=deepcopy(graph);bad_graph.rows[mapping[5]]=(op(L,'inc'),mapping[4])
    bad_invariant=deepcopy(invariant);slot=grammar['registers'].index(Q);index=graph.indices[incoming[0][0]]
    word=bad_invariant['states_at_occurrences'][index]
    bad_invariant['states_at_occurrences'][index]=word[:slot]+'3'+word[slot+1:]
    bad_sharing=dict(sharing);bad_sharing[Q]=bad_sharing[L]
    bad_turn=deepcopy(graph);a=incoming[0][0];row=bad_turn.rows[a];bad_turn.rows[a]=(row[0],row[2],row[1])
    rejected=[]
    for label,g,iv,sh in [
        ('wrong final transfer destination',bad_graph,invariant,sharing),
        ('nonzero outside-entry scratch possible',graph,bad_invariant,sharing),
        ('work aliases left',graph,invariant,bad_sharing),
        ('even turn enters swap',bad_turn,invariant,sharing),
    ]:
        try:swaps.region_premises(g,iv,sh,roles[0],pattern,turn)
        except AssertionError:rejected.append(label)
        else:raise AssertionError('region mutation accepted: '+label)
    return dict(format='np-conp-control-independent-regions-v1',reviewer='internal-model-reviewer',
        source_sha256=sha(source),checker_sha256=sha(__file__),
        dependency_pins={str(CLOSED.relative_to(COMPACT)):sha(CLOSED),str(SWAP.relative_to(COMPACT)):sha(SWAP)},
        changed_clock_roles=dict(output='main.n',length_master='main.e',exponent_master='main.j'),
        inherited_kernel_contracts_freshly_checked=inherited,swaps=checked,
        swap_fixtures=len(fixtures)*len(matches),swap_primitive_steps=total,mutations_rejected=rejected,
        inputs={name:sha(parent/name) for name in ('allocation.json','direct-clock.json','certificate-seed.json','three-move-swap.json',
            'pre-coalescence-grammar.json','coalescence-invariant.json','bank-coalescence.json')},
        scope='fresh actual caller and intermediate logical ownership review; dirty unrelated logical coordinates in prepared fixtures; no literal physical or blank-start claim')


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('parent','source','out'):p.add_argument('--'+name,type=Path,required=True)
    a=p.parse_args();result=run(a.parent,a.source)
    a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True,indent=2))
