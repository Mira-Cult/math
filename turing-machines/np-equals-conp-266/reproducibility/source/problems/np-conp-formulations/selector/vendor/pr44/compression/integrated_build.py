"""Build the complete compressed Horn machine; charge every physical state.

The selected runtime still has a literal five-state bootstrap. Contextual
quotienting is separately certified and is not an all-configuration quotient.
"""
from pathlib import Path
from collections import Counter
import ast,hashlib,json,sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sys.path[:0]=[str(HERE/'grammar'),str(HERE/'compiler')]
from kernel_builder import KernelBuilder
from backend import totalize_silently,leaf_paths
from build_baseline import canonicalize,grammar
from machine import emit,parse
from quotient import quotient,check_quotient
from test_natural import assert_factorable_entries_closed
from contextual_quotient import apply as contextual_quotient
from check_contextual_quotient import check as check_contextual

OPTIONS=dict(pooled_temporaries=True,share=True,forward_results=False,consume=True,
    digits=True,term_lookup=True,small_ops=False,small_compare=False,
    small_power=False,small_half=False,var_guards=True)

def parity_sites(text):
    """A reproducible cost choice, using an inherited semantics-preserving rule."""
    return sorted(f'{n.lineno}:{n.col_offset}:{type(n).__name__}'
        for n in ast.walk(ast.parse(text))
        if isinstance(n,ast.BinOp) and isinstance(n.op,ast.Mod)
        and isinstance(n.left,ast.Name) and n.left.id=='scan'
        and isinstance(n.right,ast.Constant) and n.right.value==2)

def construct(source,layouts=None,*,contextual=True,horner=False):
    if layouts is not None:raise ValueError('source register order is part of this recipe')
    text=Path(source).read_text()
    Builder=KernelBuilder
    if horner:
        from fused_horner import HornerBuilder
        Builder=HornerBuilder
    b=Builder(text,fused_consuming=True,compact_equal=True,
        countdown_division=True,refactor_options=dict(scoring='prefer-right'),
        shared_selector=True,intrinsic_sites=parity_sites(text),**OPTIONS)
    b.main();assert_factorable_entries_closed(b);b.build_machine()
    maximum=max(len(p) for p,_ in leaf_paths(b))
    if maximum>=3822 or len(b.registers)>1909:
        raise ValueError('inherited blank bootstrap bounds')
    missing=totalize_silently(b);b.tm.gc()
    raw,names=canonicalize(b)
    exact,exact_map=quotient(raw);check_quotient(raw,exact,exact_map)
    b.exact_machine=exact;b.exact_quotient=exact_map
    b.contextual_certificate=None
    if contextual:
        final,context=contextual_quotient(b,raw,names)
        b.contextual_replay=check_contextual(b,raw,final,names,context)
        b.contextual_certificate=context
        mapping=context['mapping']
    else:
        final,mapping=exact,exact_map
    return b,raw,final,names,mapping,missing,maximum

def build(source,out,*,contextual=True,horner=False):
    source,out=Path(source),Path(out)
    out.mkdir(parents=True,exist_ok=False)
    b,raw,final,names,mapping,missing,maximum=construct(source,contextual=contextual,horner=horner)
    for name,machine in [('raw.tm',raw),('exact.tm',b.exact_machine),('machine.tm',final)]:
        emit(machine,out/name)
        assert parse(out/name).rows==machine.rows
    groups={}
    def category(name):
        if name.startswith('shared.selector.'):return 'shared selector and bootstrap adapter'
        if name.startswith('0a.boot1.'):return 'blank bootstrap'
        if name in ('B','beep'):return 'event adapter'
        if name.startswith('3.'):return 'register operation entries'
        if name=='silent.sink':return 'totalization'
        if name[0].isdigit():return 'remaining engine and dispatch'
        return 'compiled arithmetic and control'
    for name,q in names.items():groups.setdefault(mapping[q],set()).add(category(name))
    profile=Counter(' + '.join(sorted(v)) for v in groups.values())
    metadata=dict(states=final.count,rows=len(final.rows),raw_states=raw.count,
        exact_states=b.exact_machine.count,registers=len(b.registers),max_leaf_path=maximum,
        source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        table_sha256=hashlib.sha256((out/'machine.tm').read_bytes()).hexdigest(),
        raw_table_sha256=hashlib.sha256((out/'raw.tm').read_bytes()).hexdigest(),
        exact_table_sha256=hashlib.sha256((out/'exact.tm').read_bytes()).hexdigest(),
        profile=dict(profile),options=OPTIONS,parity_sites=parity_sites(source.read_text()),
        fusion=b.fused_consuming_certificate,selector=b.selector_certificate,
        refactoring=b.closed_sequence_certificate,
        contextual_replay=b.contextual_replay if contextual else None,
        convention='blank tape; head0; start0; B1 exits; total binary L/R-only',
        equivalence=('source theorem plus conventional compiler/blank-runtime proof and replayed contextual invariant'
                     if contextual else 'source theorem plus conventional compiler/blank-runtime proof and exact quotient'),
        review='producer generation; independent review recorded separately')
    if horner:
        metadata['horner_fusion']=b.horner_certificate
        metadata['horner_reverse']=True
    artifacts=[('grammar.json',grammar(b)),('exact-quotient.json',b.exact_quotient),
        ('quotient.json',mapping),('metadata.json',metadata)]
    if contextual:artifacts.append(('contextual-certificate.json',b.contextual_certificate))
    for name,value in artifacts:
        (out/name).write_text(json.dumps(value,sort_keys=True,indent=2)+'\n')
    return metadata

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--source',type=Path,default=HERE/'source/source.py')
    p.add_argument('--out',type=Path,required=True);p.add_argument('--no-context',action='store_true')
    p.add_argument('--horner',action='store_true')
    a=p.parse_args();m=build(a.source,a.out,contextual=not a.no_context,horner=a.horner)
    print(json.dumps({k:m[k] for k in ('states','rows','raw_states','exact_states','registers','table_sha256','profile')},indent=2))
