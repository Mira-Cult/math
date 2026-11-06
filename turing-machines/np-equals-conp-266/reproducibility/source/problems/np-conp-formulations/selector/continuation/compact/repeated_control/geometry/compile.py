"""Complete paid experiment harness; discovery is distinct from fixed replay."""
from pathlib import Path
from collections import Counter
from contextlib import ExitStack
import argparse
import importlib.util
import json
import sys

HERE=Path(__file__).resolve().parent
CONTROL=HERE.parent
COMPACT=CONTROL.parent
sys.path.insert(0,str(COMPACT/'phase_swap'))
spec=importlib.util.spec_from_file_location('repeat_geometry_swap',COMPACT/'phase_swap/build.py')
old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old)
sys.path.insert(0,str(CONTROL));import dispatcher
base=old.baseline;co=old.build_coalesced;w=co.weak_grammar


def measure(source,out,*,plan=None,groups=None,discover=False,clock=True,seed=True,consume=True,consumed_seed=False):
    out=Path(out);source=Path(source).resolve()
    if out.exists():raise ValueError('fresh output required')
    options=dict(clock=clock,seed=seed,consume=consume)
    with old.region.installed(),old.build_experiment.installed(**options),ExitStack() as extras:
        if consumed_seed:
            sys.path.insert(0,str(CONTROL/'clock_width'))
            import consume_seed
            extras.enter_context(consume_seed.installed())
        if discover:
            preliminary,*_=co.build_native.construct(source)
            plan=w.search(preliminary)
            plan['source_sha256']=base.sha(source)
        assert plan is not None and plan['source_sha256']==base.sha(source)
        with co.installed(native=True,groups=groups) as instances,w.installed(plan):
            metadata=co.build_live.build(out,source)
    assert len(instances)==1;b=instances[0]
    cert=dispatcher.install(b)
    b.tm.gc();raw,names=base.canonicalize(b)
    final,mapping=base.quotient(raw);base.check_quotient(raw,final,mapping)
    base.emit(raw,out/'raw.tm');base.emit(final,out/'machine.tm')
    ingress=base.events.ingress(base.events.from_legacy(final),final.beep)
    base.events.check_ingress(base.events.from_legacy(final),ingress,final.beep)
    events,eventmap=base.events.quotient(ingress);base.events.check_quotient(ingress,events,eventmap)
    base.events.emit(ingress,out/'ingress-prequotient.tm');base.events.emit(events,out/'events.tm')
    categories={}
    for name,q in names.items():
        category='return delimiter scan' if name.startswith(dispatcher.PREFIX) else base.category(name)
        categories.setdefault(mapping[q],set()).add(category)
    profile=dict(sorted(Counter(' + '.join(sorted(c)) for c in categories.values()).items()))
    groups=[b.bank_coalescence_certificate['groups'][f'$coalesced.{i}'] for i in range(len(b.registers))]
    metadata.update(format='np-conp-zero-run-geometry-experiment-v1',source_lowering=options,
        raw_states=raw.count,states=final.count,event_states=events.count,rows=len(final.rows),event_rows=len(events.rows),
        raw_table_sha256=base.sha(out/'raw.tm'),table_sha256=base.sha(out/'machine.tm'),event_table_sha256=base.sha(out/'events.tm'),
        source_entry_raw_state=names['main().0'],source_entry_final_state=mapping[names['main().0']],profile=profile,
        native_runtime=b.native_half_runtime_certificate,source_sha256=base.sha(source),
        source_identical_to_284=base.sha(source)==base.sha(COMPACT/'phase_swap/source.py'),
        source_name=source.relative_to(COMPACT).as_posix(),generator_sha256=base.sha(Path(__file__)),
        dispatcher_sha256=base.sha(CONTROL/'dispatcher.py'),discovery_performed=discover,consumed_seed=consumed_seed,
        proof_status='experimental complete table; source proof and independent review required before promotion',
        initialization_proof_status='new exact blank-entry evidence required')
    artifacts={'metadata.json':metadata,'grammar.json':base.grammar(b),'names.json':names,'quotient.json':mapping,
        'weak-grammar-plan.json':plan,'groups.json':groups,'dispatcher.json':cert,
        'pre-control-grammar.json':b.weak_input_grammar,'pre-projection-grammar.json':b.pre_projection_grammar,
        'pre-coalescence-grammar.json':b.pre_coalescence_grammar,'bank-projection.json':b.bank_projection_certificate,
        'bank-coalescence.json':b.bank_coalescence_certificate,'coalescence-invariant.json':b.coalescence_invariant,
        'native-half.json':b.native_half_certificate,'native-runtime.json':b.native_half_runtime_certificate,
        'native-bank-permutation.json':b.native_bank_permutation,'direct-calls.json':b.direct_call_certificate,
        'return-forward.json':b.return_forward_certificate,'mixed-tuples.json':b.mixed_tuple_certificate,
        'new-arithmetic.json':b.arithmetic_certificate,'direct-clock.json':getattr(b,'direct_clock_certificate',[]),
        'certificate-seed.json':getattr(b,'certificate_seed_certificate',[]),
        'consumed-seed.json':getattr(b,'consumed_seed_certificate',[]),
        'whole-action.json':getattr(b,'np_action_certificate',[]),
        'consume-guard.json':getattr(b,'consume_guard_certificate',[]),
        'three-move-swap.json':b.three_move_swap_certificate,
        'control-certificate.json':dict(format='np-conp-return-geometry-control-v1',source_sha256=base.sha(source),
            core_graph_sha256=plan['graph_sha256'],before=plan['before'],after=plan['after'],moves=plan['moves'],
            contextual_output_grammar_sha256=old.jd(b.weak_input_grammar),
            finite_control_output_grammar_sha256=old.jd(b.pre_projection_grammar),
            projected_grammar_sha256=old.jd(b.pre_coalescence_grammar),final_grammar_sha256=old.jd(base.grammar(b)),
            progress='both branches and ordered retained primitives preserved; no jump-only cycle'),
        'event-quotient.json':dict(format='np-conp-ingress-event-quotient-v1',
            source_table_sha256=base.sha(out/'machine.tm'),predecessor_sha256=base.sha(out/'ingress-prequotient.tm'),
            result_sha256=base.sha(out/'events.tm'),source_B=final.beep,time_shift=-1,mapping=eventmap),
        'event-metadata.json':dict(states=events.count,rows=len(events.rows),start=events.start,
            source_sha256=base.sha(source),table_sha256=base.sha(out/'events.tm'),blank=0,head=0,
            event_rows=[[q,r,*v] for (q,r),v in sorted(events.rows.items()) if v[3]],halt_states_excluded=0,
            B_exit_parent_states=final.count,B_exit_parent_sha256=base.sha(out/'machine.tm'))}
    for name,data in artifacts.items():base.dump(out/name,data)
    return metadata


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--source',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True);p.add_argument('--plan',type=Path);p.add_argument('--groups',type=Path)
    p.add_argument('--discover',action='store_true');p.add_argument('--no-seed',action='store_true')
    p.add_argument('--consume-seed',action='store_true')
    a=p.parse_args();m=measure(a.source,a.out,plan=json.loads(a.plan.read_text()) if a.plan else None,
        groups=json.loads(a.groups.read_text()) if a.groups else None,discover=a.discover,seed=not a.no_seed,
        consumed_seed=a.consume_seed)
    print(json.dumps({k:m[k] for k in ('raw_states','states','event_states','registers','event_table_sha256')},indent=2))
