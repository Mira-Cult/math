"""Complete fixed-source NP=coNP transfer to the counted shared-selector runtime.

All source, compiler, input and output files are local to this package. No
network or other checkout is required. The source remains the frozen PR53
source. Exact row-event relocation is retained separately from B-exit tables.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json
import sys

HERE=Path(__file__).resolve().parent
VENDOR=HERE/'vendor/pr44'
sys.path[:0]=[str(HERE),str(HERE/'vendor'),str(VENDOR/'compression'),
    str(VENDOR/'compression/compiler'),str(VENDOR/'compression/grammar'),
    str(VENDOR/'compression/native'),str(VENDOR/'compression/source'),
    str(VENDOR/'accumulator'),str(VENDOR/'shared')]
from applicability import adapted_runtime
from kernel_builder import KernelBuilder,GenericKernelBuilder
from contextual_tree_build import ContextualTreeBuilder
from backend import totalize_silently,leaf_paths
from build_baseline import canonicalize,grammar
from machine import emit,parse
from quotient import quotient,check_quotient
from test_natural import assert_factorable_entries_closed
from contextual_quotient import apply as contextual_quotient
from check_contextual_quotient import check as check_contextual
import integrated_build
import events

SOURCE_SHA256='ae23de7359cefdd34c139e59418c54e26eddf9e207b9122cfb3473d0f52a380a'
CASES=('generic','positive','tree','selected')
BASE_OPTIONS=dict(pooled_temporaries=True,share=True,forward_results=False,consume=True,
    digits=True,term_lookup=True,small_ops=False,small_compare=False,
    small_power=False,small_half=False,var_guards=True)


def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def dump(path,value):Path(path).write_text(json.dumps(value,sort_keys=True,indent=2)+'\n')

def check_inputs():
    manifest=json.loads((HERE/'provenance.json').read_text())
    for entry in manifest['files']:
        if sha(HERE/entry['path'])!=entry['sha256']:
            raise ValueError(('pinned input changed',entry['path']))
    return manifest


def construct(source=HERE/'source.py',*,case='selected',contextual=None):
    """Return builder, raw, final, names, map, missing rows, max path.

    Source may be an explicit finite test fixture. Only build() credits the
    complete beeper, after enforcing its exact mathematical-source hash.
    """
    if case not in CASES:raise ValueError(case)
    if contextual is None: contextual = case != 'selected'
    check_inputs()
    text=Path(source).read_text()
    options={**BASE_OPTIONS}
    if case=='selected':options.update(small_ops=True,small_half=True)
    Builder=GenericKernelBuilder if case=='generic' else KernelBuilder
    if case in ('tree','selected'):Builder=ContextualTreeBuilder
    with adapted_runtime():
        b=Builder(text,fused_consuming=True,compact_equal=True,
            countdown_division=case!='generic',refactor_options=dict(scoring='prefer-right'),
            shared_selector=True,intrinsic_sites=integrated_build.parity_sites(text),**options)
        b.main();assert_factorable_entries_closed(b);b.build_machine()
    maximum=max(len(p) for p,_ in leaf_paths(b))
    if maximum>=3822 or len(b.registers)>1909:
        raise ValueError('counted blank bootstrap bounds')
    missing=totalize_silently(b);b.tm.gc()
    raw,names=canonicalize(b)
    exact,exact_map=quotient(raw);check_quotient(raw,exact,exact_map)
    b.exact_machine=exact;b.exact_quotient=exact_map
    b.contextual_certificate=None;b.contextual_replay=None
    if contextual:
        final,certificate=contextual_quotient(b,raw,names)
        b.contextual_replay=check_contextual(b,raw,final,names,certificate)
        b.contextual_certificate=certificate;mapping=certificate['mapping']
    else:final,mapping=exact,exact_map
    b.transfer_options=options;b.transfer_case=case
    return b,raw,final,names,mapping,missing,maximum


def category(name):
    if name.startswith('shared.selector.'):return 'shared selector and bootstrap adapter'
    if name.startswith('0a.boot1.'):return 'blank bootstrap'
    if name in ('B','beep'):return 'event adapter'
    if name.startswith('3.'):return 'register operation entries'
    if name=='silent.sink':return 'totalization'
    if name[0].isdigit():return 'remaining engine and dispatch'
    return 'compiled arithmetic and control'


def build(out,*,case='selected',source=HERE/'source.py',contextual=None):
    source,out=Path(source),Path(out)
    if out.exists():raise ValueError('use a fresh output directory')
    if sha(source)!=SOURCE_SHA256:raise ValueError('complete beeper requires frozen NP=coNP source')
    b,raw,final,names,mapping,missing,maximum=construct(source,case=case,contextual=contextual)
    out.mkdir(parents=True)
    for name,m in [('raw.tm',raw),('exact.tm',b.exact_machine),('machine.tm',final)]:
        emit(m,out/name)
        if parse(out/name).rows!=m.rows:raise AssertionError('literal table round trip')
    groups={}
    for name,q in names.items():groups.setdefault(mapping[q],set()).add(category(name))
    profile=dict(Counter(' + '.join(sorted(values)) for values in groups.values()))
    if sum(profile.values())!=final.count:raise AssertionError('incomplete physical partition')
    metadata=dict(format='np-conp-shared-selector-complete-v1',case=case,
        states=final.count,rows=len(final.rows),raw_states=raw.count,
        exact_states=b.exact_machine.count,registers=len(b.registers),
        source_sha256=sha(source),table_sha256=sha(out/'machine.tm'),
        raw_table_sha256=sha(out/'raw.tm'),exact_table_sha256=sha(out/'exact.tm'),
        profile=profile,options=b.transfer_options,
        source_changed=False,blank=0,head=0,start=final.start,B=final.beep,
        alphabet=[0,1],moves=['L','R'],tape_geometry='two-way infinite',
        event_convention='exit from B, before applying its row',halt_states_excluded=0,
        max_leaf_path=maximum,bootstrap_bank_anchor_after_translation=3824,
        bootstrap_zero_register_capacity=1909,bootstrap_verified_bounds=True,
        tuple_positivity=getattr(b,'positivity_certificates',None),
        totalization_requests=missing,
        contextual_replay=b.contextual_replay,
        contextual_physical_quotient=b.contextual_certificate is not None,
        source_entry='main().0',source_entry_raw_state=names['main().0'],
        source_entry_final_state=mapping[names['main().0']],
        register_order=list(b.registers),
        event_equivalence='ordered source events; each simulated finite stage completes',
        initialization_proof_status='requires separate exact blank-entry replay',
        proof_status='conventional proofs and finite certificates; no proof-assistant certification',
        producer_sources={name:sha(HERE/name) for name in ('build.py','applicability.py')})
    artifacts=[('grammar.json',grammar(b)),('names.json',names),('quotient.json',mapping),
        ('exact-quotient.json',b.exact_quotient),('metadata.json',metadata),
        ('dead-entry-extension.json',b.dead_entry_extension),
        ('selector.json',b.selector_certificate),('refactoring.json',b.closed_sequence_certificate),
        ('fusion.json',b.fused_consuming_certificate)]
    if b.contextual_certificate is not None:artifacts.append(('contextual-certificate.json',b.contextual_certificate))
    if case in ('tree','selected'):
        artifacts.extend([('contextual-tree-certificate.json',b.contextual_tree_certificate),
            ('countdown.json',b.countdown_certificate),('horner.json',b.horner_certificate)])
    for name,value in artifacts:dump(out/name,value)
    # Event shift changes no physical action and has a total bijection t <-> t+1.
    prior=events.from_legacy(final)
    shifted=events.ingress(prior,final.beep);events.check_ingress(prior,shifted,final.beep)
    event,event_map=events.quotient(shifted);events.check_quotient(shifted,event,event_map)
    events.emit(shifted,out/'ingress-prequotient.tm');events.emit(event,out/'events.tm')
    dump(out/'event-quotient.json',dict(format='np-conp-ingress-event-quotient-v1',
        source_table_sha256=sha(out/'machine.tm'),predecessor_sha256=sha(out/'ingress-prequotient.tm'),
        result_sha256=sha(out/'events.tm'),source_B=final.beep,time_shift=-1,mapping=event_map))
    dump(out/'event-metadata.json',dict(states=event.count,rows=len(event.rows),start=event.start,
        source_sha256=SOURCE_SHA256,table_sha256=sha(out/'events.tm'),blank=0,head=0,
        tape_geometry='two-way infinite',moves=['L','R'],halt_states_excluded=0,
        event_convention='sixth table column; marked transition applied',
        event_rows=[[q,r,*v] for (q,r),v in sorted(event.rows.items()) if v[3]],
        B_exit_parent_states=final.count,B_exit_parent_sha256=sha(out/'machine.tm'),
        relation='event on ingress exactly one physical step before former B exit; exact quotient'))
    return metadata


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True)
    p.add_argument('--case',choices=CASES,default='selected')
    p.add_argument('--contextual',action='store_true',help='explicit comparison; final selected default uses exact all-row quotient')
    a=p.parse_args()
    m=build(a.out,case=a.case,contextual=True if a.contextual else None)
    print(json.dumps({k:m[k] for k in ('case','states','rows','raw_states','exact_states','table_sha256','profile')},indent=2))
