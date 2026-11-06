"""Replay complete inline phase candidates using only published fixed inputs."""
from pathlib import Path
import argparse
import hashlib
import json
import sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'transfer328/coordinator'))
import build_experiment
import region

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent/'transfer328'
COMPACT=ROOT.parent
build_coalesced=build_experiment.build_coalesced
baseline=build_coalesced.baseline
CASES=json.loads((HERE/'recipes.json').read_text())


def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def jd(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def inputs(case):
    recipe=CASES[case]
    source=HERE/recipe['source'];planfile=HERE/'plans'/case/'grammar.json'
    groupfile=HERE/'plans'/case/'groups.json'
    plan=json.loads(planfile.read_text());groups=json.loads(groupfile.read_text())
    assert sha(source)==plan['source_sha256']
    return recipe,source,planfile,groupfile,plan,groups


def construct(case='swap290'):
    recipe,source,_,_,plan,groups=inputs(case)
    with region.installed(), build_experiment.installed(**recipe['options']):
        with build_coalesced.installed(native=True,groups=groups):
            with build_coalesced.weak_grammar.installed(plan):
                return build_coalesced.build_live.construct(source)


def build(out,case='swap290'):
    out=Path(out)
    if out.exists():raise ValueError('fresh output directory required')
    recipe,source,planfile,groupfile,plan,groups=inputs(case)
    with region.installed(), build_experiment.installed(**recipe['options']):
        with build_coalesced.installed(native=True,groups=groups) as instances:
            with build_coalesced.weak_grammar.installed(plan):
                m=build_coalesced.build_live.build(out,source)
    assert len(instances)==1
    b=instances[0];final=baseline.grammar(b)
    assert jd(b.weak_input_grammar)==b.contextual_tree_certificate['output_grammar_sha256']
    assert jd(b.pre_projection_grammar)==b.bank_projection_certificate['before_grammar_sha256']
    assert jd(b.pre_coalescence_grammar)==b.bank_projection_certificate['after_grammar_sha256']==b.bank_coalescence_certificate['before_grammar_sha256']
    assert jd(final)==b.bank_coalescence_certificate['after_grammar_sha256']
    assert jd(b.coalescence_invariant)==b.bank_coalescence_certificate['invariant_sha256']
    assert groups==[b.bank_coalescence_certificate['groups'][f'$coalesced.{i}'] for i in range(len(groups))]
    producers=[Path(__file__),ROOT/'coordinator/build_experiment.py',HERE/'recipes.json',HERE/'region.py',source,planfile,groupfile]
    for option,path in [('clock',ROOT/'control/clock_region.py'),('seed',ROOT/'control/seed_region.py'),
                        ('action',ROOT/'physical/region.py'),('consume',ROOT/'coordinator/consume_guard.py')]:
        if recipe['options'].get(option):producers.append(path)
    producers += [Path(build_experiment.build_parser.__file__),Path(build_experiment.build_parser.build_skip.__file__)]
    m.update(format='np-conp-three-transfer-swap-complete-v1',architecture=case,
        totalization_requests=sorted(m['totalization_requests']),source_sha256=sha(source),
        selected_semantics='normalized pairs; both acceptance phases existential; same returned bits and outer event/comparison order',
        source_theorem='PROOF.md plus ../transfer328/PROOF.md',fixed_plan=True,optimization_search=False,
        native_runtime=b.native_half_runtime_certificate,source_lowering=recipe['options'],
        producer_inputs={p.relative_to(COMPACT).as_posix():sha(p) for p in producers},
        contextual_tree_certificate_scope='pre-control-grammar.json; native-aware HALF transfer',
        finite_control_certificate_scope='pre-control-grammar.json to pre-projection-grammar.json',
        projection_certificate_scope='pre-projection-grammar.json to pre-coalescence-grammar.json',
        coalescence_certificate_scope='pre-coalescence-grammar.json to grammar.json; every intermediate primitive ownership',
        allocation_certificate_scope='new source CFG plus explicit clock/seed lifetime edges; exact swap region refinement in PROOF.md and inherited closed-region proofs',
        review_status='author producer; independent reviews bind a separate immutable commit',
        source_unchanged_from=dict(producer='81147084e3d81219073ba6b8f0e6a3e3af8cf116',
            path='transfer328/control/attempt_reset/source.py',sha256=sha(source)))
    artifacts={'metadata.json':m,'pre-control-grammar.json':b.weak_input_grammar,
        'pre-projection-grammar.json':b.pre_projection_grammar,'pre-coalescence-grammar.json':b.pre_coalescence_grammar,
        'bank-projection.json':b.bank_projection_certificate,'bank-coalescence.json':b.bank_coalescence_certificate,
        'coalescence-invariant.json':b.coalescence_invariant,'native-half.json':b.native_half_certificate,
        'native-runtime.json':b.native_half_runtime_certificate,'native-bank-permutation.json':b.native_bank_permutation,
        'direct-calls.json':b.direct_call_certificate,'return-forward.json':b.return_forward_certificate,
        'mixed-tuples.json':b.mixed_tuple_certificate,'new-arithmetic.json':b.arithmetic_certificate,
        'direct-clock.json':getattr(b,'direct_clock_certificate',[]),
        'certificate-seed.json':getattr(b,'certificate_seed_certificate',[]),
        'consume-guard.json':getattr(b,'consume_guard_certificate',[]),
        'whole-action.json':getattr(b,'np_action_certificate',[]),
        'three-move-swap.json':b.three_move_swap_certificate,
        'control-certificate.json':dict(format='np-conp-transfer-inline-control-v1',source_sha256=sha(source),
            plan_sha256=sha(planfile),groups_sha256=sha(groupfile),core_graph_sha256=plan['graph_sha256'],
            before=plan['before'],after=plan['after'],moves=plan['moves'],
            contextual_output_grammar_sha256=jd(b.weak_input_grammar),finite_control_output_grammar_sha256=jd(b.pre_projection_grammar),
            projected_grammar_sha256=jd(b.pre_coalescence_grammar),final_grammar_sha256=jd(final),
            progress='positive finite retained primitives; finite administrative contractions have no jump-only cycle',
            event_scope='source event order; marked ingress precedes companion B exit by one transition')}
    for name,value in artifacts.items():baseline.dump(out/name,value)
    assert [m[k] for k in ('raw_states','states','event_states')]==recipe['counts']
    assert sha(out/'events.tm')==recipe['events_sha256']
    return m


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--case',choices=CASES,default='swap290');p.add_argument('--out',type=Path,required=True)
    a=p.parse_args();m=build(a.out,a.case)
    print(json.dumps({k:m[k] for k in ('raw_states','states','event_states','registers','event_table_sha256')},sort_keys=True,indent=2))
